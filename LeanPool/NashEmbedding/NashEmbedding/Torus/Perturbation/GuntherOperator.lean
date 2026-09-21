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
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.GuntherIteration
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.ConvolutionAlgebra
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.MultiplicationBootstrap

/-!
# The Günther operator on the momentum side

Theorem B is the statement that, for a free embedding `u⁰` and a small perturbation `h`
of the induced metric, the equation `∂ᵢu·∂ⱼu = g⁰ᵢⱼ + hᵢⱼ` for `u = u⁰ + v` can be solved by
a fixed point `v = T v` with

  `T v = -∑ᵢ Fᵢ(v) aᵢ + ∑_{p≤q} ½ (U_{pq}(v) - h_{pq}) b_{pq}`,

where `aᵢ, b_{pq}` is the dual frame of `{∂ᵢu⁰} ∪ {∂ᵢ∂ⱼu⁰}_{i≤j}` (`DualFrame.lean`) and,
with `L = ∑ₖ ∂ₖ²` and `R = (I - L)⁻¹`,

  `Fᵢ(v) = -R(Lv · ∂ᵢv)`,
  `Uᵢⱼ(v) = R(∂ᵢv · ∂ⱼv) + 2 R(Lv · ∂ᵢ∂ⱼv) - 2 R(∑ₖ ∂ᵢ∂ₖv · ∂ⱼ∂ₖv)`.

This file defines `T` on vector coefficient sequences (`VecSeq`), in the polarized form
`T v = c + B v v` with `B` bilinear, and proves the hypotheses `IterHyp` of the abstract
iteration (`GuntherIteration.lean`):

* multiplication is coefficient convolution (`seqConv`), the dot product is `dotConv`,
  derivatives are `partialCoeff` componentwise, `R` is `resolventCoeff`;
* every ingredient is a *tame bilinear map*: a bilinear `Q` with
    `‖Q v w‖²_(k) ≤ A' (‖v‖²_(k)‖w‖²_(r) + ‖v‖²_(r)‖w‖²_(k)) + Bₖ · lower_k(v, w)`
  for all `k ≥ r`, `A'` independent of `k` (`ScalarTame`, `VecTame`);
* tame maps are closed under sums, real scalings, and multiplication by a fixed rapidly
  decaying sequence (MT3 with `r' = r`), and `R(D₁v · D₂w)` is tame for derivative
  operators `D₁, D₂` of order `≤ 2` (MT3 at level `k - 2` with `r' = r - 2`), which
  is why the base level must satisfy `n/2 + 3 < r`.

All constants are explicit `def`s; no attempt is made to optimize them.
-/

open scoped BigOperators
open Filter Topology NashEmbedding.Sobolev

noncomputable section

namespace NashEmbedding

variable {n N : ℕ}

/-- Scalar coefficient sequences. -/
abbrev Seq (n : ℕ) := (Fin n → ℤ) → ℂ

/-! ## Operations on vector sequences -/

/-- Componentwise `∂ᵢ`. -/
def vpartial (i : Fin n) (v : VecSeq n N) : VecSeq n N := fun α => partialCoeff i (v α)

/-- Componentwise `L = ∑ₖ ∂ₖ² = -Δ`, i.e. the multiplier `-|m|²`. -/
def vlap (v : VecSeq n N) : VecSeq n N := fun α m => -(laplacianCoeff (v α) m)

/-- Componentwise `R = (I - L)⁻¹ = (I + Δ)⁻¹`. -/
def vresolvent (v : VecSeq n N) : VecSeq n N := fun α => resolventCoeff (v α)

/-- The dot product of two vector sequences: `∑ α, (v α) ⊛ (w α)`. -/
def dotConv (v w : VecSeq n N) : Seq n := fun m => ∑ α, seqConv (v α) (w α) m

/-- Multiplication of a vector sequence by a scalar sequence: `(f ⊛ a α)_α`. -/
def smulSeq (f : Seq n) (a : VecSeq n N) : VecSeq n N := fun α => seqConv f (a α)

/-- The lower-order bucket of the tame estimate at level `k`:
`‖v‖²_(k-1)‖w‖²_(r) + ‖v‖²_(r)‖w‖²_(k-1) + ‖v‖²_(r)‖w‖²_(r)`. -/
def lower (n N : ℕ) (r k : ℕ) (v w : VecSeq n N) : ℝ :=
  vecNormSq n N ((k - 1 : ℕ) : ℝ) v * vecNormSq n N r w
    + vecNormSq n N r v * vecNormSq n N ((k - 1 : ℕ) : ℝ) w
    + vecNormSq n N r v * vecNormSq n N r w

/-- The top-order bucket: `‖v‖²_(k)‖w‖²_(r) + ‖v‖²_(r)‖w‖²_(k)`. -/
def top (n N : ℕ) (r k : ℕ) (v w : VecSeq n N) : ℝ :=
  vecNormSq n N k v * vecNormSq n N r w + vecNormSq n N r v * vecNormSq n N k w

lemma lower_nonneg (r k : ℕ) (v w : VecSeq n N) : 0 ≤ lower n N r k v w := by
  unfold lower
  have h := vecNormSq_nonneg (n := n) (N := N)
  exact add_nonneg (add_nonneg (mul_nonneg (h _ _) (h _ _)) (mul_nonneg (h _ _) (h _ _)))
    (mul_nonneg (h _ _) (h _ _))

lemma top_nonneg (r k : ℕ) (v w : VecSeq n N) : 0 ≤ top n N r k v w := by
  unfold top
  have h := vecNormSq_nonneg (n := n) (N := N)
  exact add_nonneg (mul_nonneg (h _ _) (h _ _)) (mul_nonneg (h _ _) (h _ _))

/-- For `k ≥ r`, `lower_k ≤ 3 top_k`… we only need: `‖v‖²_(r)‖w‖²_(r) ≤ top_k`. -/
lemma vecNormSq_mul_le_top {r k : ℕ} (hk : r ≤ k) {v w : VecSeq n N}
    (hv : VMem n N k v) (hw : VMem n N k w) :
    vecNormSq n N r v * vecNormSq n N r w ≤ top n N r k v w := by
  unfold top
  have hrk : ((r : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk
  have hvm : vecNormSq n N r v ≤ vecNormSq n N k v := vecNormSq_mono hv hrk
  have hv0 : 0 ≤ vecNormSq n N ((r : ℕ) : ℝ) v := vecNormSq_nonneg _ _
  have hw0 : 0 ≤ vecNormSq n N ((r : ℕ) : ℝ) w := vecNormSq_nonneg _ _
  have hwk : 0 ≤ vecNormSq n N ((k : ℕ) : ℝ) w := vecNormSq_nonneg _ _
  nlinarith

/-- Monotonicity of the lower bucket in `k` (for `r ≤ k`). -/
lemma lower_mono {r k : ℕ} (hk : r ≤ k) {v w : VecSeq n N}
    (hv : VMem n N (k + 1 : ℕ) v) (hw : VMem n N (k + 1 : ℕ) w) :
    lower n N r k v w ≤ lower n N r (k + 1) v w := by
  unfold lower
  simp only [Nat.add_sub_cancel]
  have hkk : ((k : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hvk : VMem n N ((k : ℕ) : ℝ) v := hv.mono hkk
  have hwk : VMem n N ((k : ℕ) : ℝ) w := hw.mono hkk
  have hsub : ((k - 1 : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le k 1
  have hv1 : vecNormSq n N ((k - 1 : ℕ) : ℝ) v ≤ vecNormSq n N ((k : ℕ) : ℝ) v :=
    vecNormSq_mono hvk hsub
  have hw1 : vecNormSq n N ((k - 1 : ℕ) : ℝ) w ≤ vecNormSq n N ((k : ℕ) : ℝ) w :=
    vecNormSq_mono hwk hsub
  have hv0 : 0 ≤ vecNormSq n N ((r : ℕ) : ℝ) v := vecNormSq_nonneg _ _
  have hw0 : 0 ≤ vecNormSq n N ((r : ℕ) : ℝ) w := vecNormSq_nonneg _ _
  nlinarith

/-- `top_k ≤ lower_{k+1}`. -/
lemma top_le_lower_succ (r k : ℕ) (v w : VecSeq n N) :
    top n N r k v w ≤ lower n N r (k + 1) v w := by
  unfold top lower
  simp only [Nat.add_sub_cancel]
  have hv0 : 0 ≤ vecNormSq n N ((r : ℕ) : ℝ) v := vecNormSq_nonneg _ _
  have hw0 : 0 ≤ vecNormSq n N ((r : ℕ) : ℝ) w := vecNormSq_nonneg _ _
  nlinarith

/-! ## Derivative operators -/

/-- A linear operator on vector sequences that lowers the Sobolev level by `d` with
norm at most `1`: `id` (`d = 0`), `∂ᵢ` (`d = 1`), `∂ᵢ∂ⱼ` and `L` (`d = 2`). -/
structure IsDerivOp (D : VecSeq n N → VecSeq n N) (d : ℕ) : Prop where
  sub : ∀ v w, D (v - w) = D v - D w
  mem : ∀ (s : ℝ) (v : VecSeq n N), VMem n N (s + d) v → VMem n N s (D v)
  bound : ∀ (s : ℝ) (v : VecSeq n N), VMem n N (s + d) v →
    vecNormSq n N s (D v) ≤ vecNormSq n N (s + d) v

lemma isDerivOp_id : IsDerivOp (n := n) (N := N) id 0 := by
  refine ⟨fun v w => rfl, ?_, ?_⟩
  · intro s v hv
    simpa using hv
  · intro s v _
    simp

lemma isDerivOp_vpartial (i : Fin n) : IsDerivOp (vpartial (N := N) i) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v w
    funext α m
    simp only [vpartial, partialCoeff, Pi.sub_apply]
    ring
  · intro s v hv α
    have h : MemSobolev n (s + 1) (v α) := by simpa using hv α
    exact memSobolev_partialCoeff h i
  · intro s v hv
    unfold vecNormSq
    refine Finset.sum_le_sum fun α _ => ?_
    have h : MemSobolev n (s + 1) (v α) := by simpa using hv α
    have := sobolevNormSq_partialCoeff_le h i
    simpa [vpartial] using this

lemma isDerivOp_vlap : IsDerivOp (vlap (n := n) (N := N)) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v w
    funext α m
    simp only [vlap, laplacianCoeff, Pi.sub_apply]
    ring
  · intro s v hv α
    have h : MemSobolev n (s + 2) (v α) := by simpa using hv α
    exact (memSobolev_laplacianCoeff h).neg
  · intro s v hv
    unfold vecNormSq
    refine Finset.sum_le_sum fun α _ => ?_
    have h : MemSobolev n (s + 2) (v α) := by simpa using hv α
    have hb := sobolevNormSq_laplacianCoeff_le h
    have he : sobolevNormSq n s (vlap v α) = sobolevNormSq n s (laplacianCoeff (v α)) :=
      sobolevNormSq_neg s (laplacianCoeff (v α))
    rw [he]
    simpa using hb

lemma IsDerivOp.comp {D₁ D₂ : VecSeq n N → VecSeq n N} {d₁ d₂ : ℕ}
    (h₁ : IsDerivOp D₁ d₁) (h₂ : IsDerivOp D₂ d₂) : IsDerivOp (fun v => D₁ (D₂ v)) (d₁ + d₂) := by
  have hcast : ∀ s : ℝ, s + ((d₁ + d₂ : ℕ) : ℝ) = (s + (d₂ : ℝ)) + (d₁ : ℝ) := by
    intro s; push_cast; ring
  refine ⟨?_, ?_, ?_⟩
  · intro v w
    rw [h₂.sub, h₁.sub]
  · intro s v hv
    rw [hcast s] at hv
    exact h₁.mem s _ (h₂.mem (s + (d₁ : ℝ)) v (by rw [add_right_comm]; exact hv))
  · intro s v hv
    rw [hcast s] at hv ⊢
    have h2 : VMem n N (s + (d₁ : ℝ)) (D₂ v) :=
      h₂.mem (s + (d₁ : ℝ)) v (by rw [add_right_comm]; exact hv)
    calc vecNormSq n N s (D₁ (D₂ v)) ≤ vecNormSq n N (s + (d₁ : ℝ)) (D₂ v) :=
          h₁.bound s _ h2
      _ ≤ vecNormSq n N ((s + (d₁ : ℝ)) + (d₂ : ℝ)) v :=
          h₂.bound (s + (d₁ : ℝ)) v (by rw [add_right_comm]; exact hv)
      _ = vecNormSq n N ((s + (d₂ : ℝ)) + (d₁ : ℝ)) v := by rw [add_right_comm]

lemma isDerivOp_vpartial_vpartial (i j : Fin n) :
    IsDerivOp (fun v : VecSeq n N => vpartial i (vpartial j v)) 2 :=
  (isDerivOp_vpartial i).comp (isDerivOp_vpartial j)

/-! ## Tame bilinear maps -/

/-- A scalar-valued bilinear map of vector sequences with a `k`-uniform tame estimate at all
levels `k ≥ r`. `sub_left`/`sub_right` are the bilinearity we need (for polarization). -/
structure ScalarTame (n N r : ℕ) (Q : VecSeq n N → VecSeq n N → Seq n) (A' : ℝ) (Bk : ℕ → ℝ) :
    Prop where
  A'_nonneg : 0 ≤ A'
  Bk_nonneg : ∀ k, 0 ≤ Bk k
  mem : ∀ k : ℕ, r ≤ k → ∀ v w, VMem n N k v → VMem n N k w → MemSobolev n k (Q v w)
  bound : ∀ k : ℕ, r ≤ k → ∀ v w, VMem n N k v → VMem n N k w →
    sobolevNormSq n k (Q v w) ≤ A' * top n N r k v w + Bk k * lower n N r k v w
  sub_left : ∀ v v' w, VMem n N r v → VMem n N r v' → VMem n N r w →
    Q (v - v') w = fun m => Q v w m - Q v' w m
  sub_right : ∀ v w w', VMem n N r v → VMem n N r w → VMem n N r w' →
    Q v (w - w') = fun m => Q v w m - Q v w' m

/-- Vector-valued version. -/
structure VecTame (n N r : ℕ) (Q : VecSeq n N → VecSeq n N → VecSeq n N) (A' : ℝ) (Bk : ℕ → ℝ) :
    Prop where
  A'_nonneg : 0 ≤ A'
  Bk_nonneg : ∀ k, 0 ≤ Bk k
  mem : ∀ k : ℕ, r ≤ k → ∀ v w, VMem n N k v → VMem n N k w → VMem n N k (Q v w)
  bound : ∀ k : ℕ, r ≤ k → ∀ v w, VMem n N k v → VMem n N k w →
    vecNormSq n N k (Q v w) ≤ A' * top n N r k v w + Bk k * lower n N r k v w
  sub_left : ∀ v v' w, VMem n N r v → VMem n N r v' → VMem n N r w →
    Q (v - v') w = Q v w - Q v' w
  sub_right : ∀ v w w', VMem n N r v → VMem n N r w → VMem n N r w' →
    Q v (w - w') = Q v w - Q v w'

/-! ### Combinators -/

lemma ScalarTame.add {r : ℕ} {Q₁ Q₂ : VecSeq n N → VecSeq n N → Seq n} {A₁ A₂ : ℝ} {B₁ B₂ : ℕ → ℝ}
    (h₁ : ScalarTame n N r Q₁ A₁ B₁) (h₂ : ScalarTame n N r Q₂ A₂ B₂) :
    ScalarTame n N r (fun v w m => Q₁ v w m + Q₂ v w m) (2 * (A₁ + A₂)) (fun k => 2 * (B₁ k + B₂
        k)) := by
  refine ⟨by linarith [h₁.A'_nonneg, h₂.A'_nonneg], fun k => by
    linarith [h₁.Bk_nonneg k, h₂.Bk_nonneg k], ?_, ?_, ?_, ?_⟩
  · intro k hk v w hv hw
    exact (h₁.mem k hk v w hv hw).add (h₂.mem k hk v w hv hw)
  · intro k hk v w hv hw
    have hb₁ := h₁.bound k hk v w hv hw
    have hb₂ := h₂.bound k hk v w hv hw
    have hadd := sobolevNormSq_add_le (h₁.mem k hk v w hv hw) (h₂.mem k hk v w hv hw)
    linarith
  · intro v v' w hv hv' hw
    have e₁ : ∀ m, Q₁ (v - v') w m = Q₁ v w m - Q₁ v' w m :=
      fun m => congrFun (h₁.sub_left v v' w hv hv' hw) m
    have e₂ : ∀ m, Q₂ (v - v') w m = Q₂ v w m - Q₂ v' w m :=
      fun m => congrFun (h₂.sub_left v v' w hv hv' hw) m
    funext m
    rw [e₁ m, e₂ m]
    ring
  · intro v w w' hv hw hw'
    have e₁ : ∀ m, Q₁ v (w - w') m = Q₁ v w m - Q₁ v w' m :=
      fun m => congrFun (h₁.sub_right v w w' hv hw hw') m
    have e₂ : ∀ m, Q₂ v (w - w') m = Q₂ v w m - Q₂ v w' m :=
      fun m => congrFun (h₂.sub_right v w w' hv hw hw') m
    funext m
    rw [e₁ m, e₂ m]
    ring

lemma ScalarTame.const_mul {r : ℕ} {Q : VecSeq n N → VecSeq n N → Seq n} {A' : ℝ} {Bk : ℕ → ℝ}
    (h : ScalarTame n N r Q A' Bk) (c : ℝ) :
    ScalarTame n N r (fun v w m => (c : ℂ) * Q v w m) (c ^ 2 * A') (fun k => c ^ 2 * Bk k) := by
  have hc2 : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
  have hnorm : ‖(c : ℂ)‖ ^ 2 = c ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨mul_nonneg hc2 h.A'_nonneg, fun k => mul_nonneg hc2 (h.Bk_nonneg k), ?_, ?_, ?_, ?_⟩
  · intro k hk v w hv hw
    exact (h.mem k hk v w hv hw).smul (c : ℂ)
  · intro k hk v w hv hw
    have hb := h.bound k hk v w hv hw
    have heq : sobolevNormSq n k (fun m => (c : ℂ) * Q v w m) = c ^ 2 * sobolevNormSq n k (Q v
        w) := by
      rw [sobolevNormSq_smul, hnorm]
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hb hc2]
  · intro v v' w hv hv' hw
    have e : ∀ m, Q (v - v') w m = Q v w m - Q v' w m :=
      fun m => congrFun (h.sub_left v v' w hv hv' hw) m
    funext m
    rw [e m]
    ring
  · intro v w w' hv hw hw'
    have e : ∀ m, Q v (w - w') m = Q v w m - Q v w' m :=
      fun m => congrFun (h.sub_right v w w' hv hw hw') m
    funext m
    rw [e m]
    ring

lemma ScalarTame.neg {r : ℕ} {Q : VecSeq n N → VecSeq n N → Seq n} {A' : ℝ} {Bk : ℕ → ℝ}
    (h : ScalarTame n N r Q A' Bk) : ScalarTame n N r (fun v w m => -Q v w m) A' Bk := by
  refine ⟨h.A'_nonneg, h.Bk_nonneg, ?_, ?_, ?_, ?_⟩
  · intro k hk v w hv hw
    exact (h.mem k hk v w hv hw).neg
  · intro k hk v w hv hw
    rw [sobolevNormSq_neg]
    exact h.bound k hk v w hv hw
  · intro v v' w hv hv' hw
    have e : ∀ m, Q (v - v') w m = Q v w m - Q v' w m :=
      fun m => congrFun (h.sub_left v v' w hv hv' hw) m
    funext m
    rw [e m]
    ring
  · intro v w w' hv hw hw'
    have e : ∀ m, Q v (w - w') m = Q v w m - Q v w' m :=
      fun m => congrFun (h.sub_right v w w' hv hw hw') m
    funext m
    rw [e m]
    ring

lemma ScalarTame.finset_sum {ι : Type*} {r : ℕ} (S : Finset ι)
    {Q : ι → VecSeq n N → VecSeq n N → Seq n} {A' : ι → ℝ} {Bk : ι → ℕ → ℝ}
    (h : ∀ i ∈ S, ScalarTame n N r (Q i) (A' i) (Bk i)) :
    ScalarTame n N r (fun v w m => ∑ i ∈ S, Q i v w m) (S.card * ∑ i ∈ S, A' i)
      (fun k => S.card * ∑ i ∈ S, Bk i k) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i hi => (h i hi).A'_nonneg),
    fun k => mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun i hi => (h i hi).Bk_nonneg k), ?_, ?_, ?_, ?_⟩
  · intro k hk v w hv hw
    exact MemSobolev.finset_sum S fun i hi => (h i hi).mem k hk v w hv hw
  · intro k hk v w hv hw
    calc sobolevNormSq n k (fun m => ∑ i ∈ S, Q i v w m)
        ≤ S.card * ∑ i ∈ S, sobolevNormSq n k (Q i v w) :=
          sobolevNormSq_finset_sum_le S fun i hi => (h i hi).mem k hk v w hv hw
      _ ≤ S.card * ∑ i ∈ S, (A' i * top n N r k v w + Bk i k * lower n N r k v w) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum fun i hi => (h i hi).bound k hk v w hv hw
      _ = (S.card * ∑ i ∈ S, A' i) * top n N r k v w
            + (S.card * ∑ i ∈ S, Bk i k) * lower n N r k v w := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
  · intro v v' w hv hv' hw
    funext m
    have e : ∀ i ∈ S, Q i (v - v') w m = Q i v w m - Q i v' w m :=
      fun i hi => congrFun ((h i hi).sub_left v v' w hv hv' hw) m
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl e
  · intro v w w' hv hw hw'
    funext m
    have e : ∀ i ∈ S, Q i v (w - w') m = Q i v w m - Q i v w' m :=
      fun i hi => congrFun ((h i hi).sub_right v w w' hv hw hw') m
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl e

lemma VecTame.add {r : ℕ} {Q₁ Q₂ : VecSeq n N → VecSeq n N → VecSeq n N} {A₁ A₂ : ℝ} {B₁ B₂ : ℕ → ℝ}
    (h₁ : VecTame n N r Q₁ A₁ B₁) (h₂ : VecTame n N r Q₂ A₂ B₂) :
    VecTame n N r (fun v w => Q₁ v w + Q₂ v w) (2 * (A₁ + A₂)) (fun k => 2 * (B₁ k + B₂ k)) := by
  refine ⟨by linarith [h₁.A'_nonneg, h₂.A'_nonneg], fun k => by
    linarith [h₁.Bk_nonneg k, h₂.Bk_nonneg k], ?_, ?_, ?_, ?_⟩
  · intro k hk v w hv hw
    exact (h₁.mem k hk v w hv hw).add (h₂.mem k hk v w hv hw)
  · intro k hk v w hv hw
    have hb₁ := h₁.bound k hk v w hv hw
    have hb₂ := h₂.bound k hk v w hv hw
    have hadd := vecNormSq_add_le (h₁.mem k hk v w hv hw) (h₂.mem k hk v w hv hw)
    linarith
  · intro v v' w hv hv' hw
    rw [h₁.sub_left v v' w hv hv' hw, h₂.sub_left v v' w hv hv' hw]
    abel
  · intro v w w' hv hw hw'
    rw [h₁.sub_right v w w' hv hw hw', h₂.sub_right v w w' hv hw hw']
    abel

lemma VecTame.neg {r : ℕ} {Q : VecSeq n N → VecSeq n N → VecSeq n N} {A' : ℝ} {Bk : ℕ → ℝ}
    (h : VecTame n N r Q A' Bk) : VecTame n N r (fun v w => -Q v w) A' Bk := by
  refine ⟨h.A'_nonneg, h.Bk_nonneg, ?_, ?_, ?_, ?_⟩
  · intro k hk v w hv hw
    exact (h.mem k hk v w hv hw).neg
  · intro k hk v w hv hw
    rw [vecNormSq_neg]
    exact h.bound k hk v w hv hw
  · intro v v' w hv hv' hw
    rw [h.sub_left v v' w hv hv' hw]
    abel
  · intro v w w' hv hw hw'
    rw [h.sub_right v w w' hv hw hw']
    abel

lemma VecTame.finset_sum {ι : Type*} {r : ℕ} (S : Finset ι)
    {Q : ι → VecSeq n N → VecSeq n N → VecSeq n N} {A' : ι → ℝ} {Bk : ι → ℕ → ℝ}
    (h : ∀ i ∈ S, VecTame n N r (Q i) (A' i) (Bk i)) :
    VecTame n N r (fun v w => ∑ i ∈ S, Q i v w) (S.card * ∑ i ∈ S, A' i)
      (fun k => S.card * ∑ i ∈ S, Bk i k) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i hi => (h i hi).A'_nonneg),
    fun k => mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg fun i hi => (h i hi).Bk_nonneg k), ?_, ?_, ?_, ?_⟩
  · intro k hk v w hv hw
    exact VMem.finset_sum S fun i hi => (h i hi).mem k hk v w hv hw
  · intro k hk v w hv hw
    calc vecNormSq n N k (∑ i ∈ S, Q i v w)
        ≤ S.card * ∑ i ∈ S, vecNormSq n N k (Q i v w) :=
          vecNormSq_finset_sum_le S fun i hi => (h i hi).mem k hk v w hv hw
      _ ≤ S.card * ∑ i ∈ S, (A' i * top n N r k v w + Bk i k * lower n N r k v w) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum fun i hi => (h i hi).bound k hk v w hv hw
      _ = (S.card * ∑ i ∈ S, A' i) * top n N r k v w
            + (S.card * ∑ i ∈ S, Bk i k) * lower n N r k v w := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          ring
  · intro v v' w hv hv' hw
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i hi => (h i hi).sub_left v v' w hv hv' hw
  · intro v w w' hv hw hw'
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i hi => (h i hi).sub_right v w w' hv hw hw'

/-- Constants for multiplication by a fixed sequence `a` in every `H^k` (MT3 with `r' = r`).
Top constant: `mt3AConstSq n r · ‖a‖²_(r) · A'`, independent of `k`. -/
def smulTopConst (n N r : ℕ) (a : VecSeq n N) (A' : ℝ) : ℝ :=
  mt3AConstSq n r * vecNormSq n N r a * A'

/-- Lower constant for multiplication by a fixed sequence (generous). -/
def smulLowConst (n N r : ℕ) (a : VecSeq n N) (A' : ℝ) (Bk : ℕ → ℝ) (k : ℕ) : ℝ :=
  (mt3AConstSq n r + mt3BConstSq n k r)
    * (vecNormSq n N r a + vecNormSq n N k a + vecNormSq n N ((k - 1 : ℕ) : ℝ) a)
    * (Bk k + Bk (k - 1) + 3 * A' + 3 * Bk r + 1)

/-- **Multiplication by a fixed rapidly decaying sequence preserves tameness.** Uses
`third_multiplication_theorem_seq` at level `k` with `r' = r` (needs `1 + n/2 < r`). -/
theorem ScalarTame.smulSeq (hn : 0 < n) {r : ℕ} (hr : 1 + (n : ℝ) / 2 < r)
    {Q : VecSeq n N → VecSeq n N → Seq n} {A' : ℝ} {Bk : ℕ → ℝ}
    (h : ScalarTame n N r Q A' Bk) (a : VecSeq n N) (ha : ∀ k : ℕ, VMem n N k a) :
    VecTame n N r (fun v w => smulSeq (Q v w) a) (smulTopConst n N r a A')
      (smulLowConst n N r a A' Bk) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr1 : (1 : ℝ) < (r : ℝ) := by linarith
  have h2r : (n : ℝ) < 2 * (r : ℝ) := by linarith
  have hA3 : 0 ≤ mt3AConstSq n (r : ℝ) := by
    have h0 : (0 : ℝ) ≤ mt3KSq n (r : ℝ) := by
      unfold mt3KSq; exact tsum_nonneg fun j => weight_nonneg _ _
    unfold mt3AConstSq; linarith
  have hB3 : ∀ j : ℕ, 0 ≤ mt3BConstSq n j (r : ℝ) := by
    intro j
    have hL : (0 : ℝ) ≤ mt3LSq n (r : ℝ) := by
      unfold mt3LSq; exact tsum_nonneg fun i => weight_nonneg _ _
    have hS : 0 ≤ mt3BStar j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · norm_num [mt3BStar]
      · exact mt3BStar_nonneg hj
    unfold mt3BConstSq
    exact mul_nonneg (mul_nonneg (by norm_num) hS) hL
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold smulTopConst
    exact mul_nonneg (mul_nonneg hA3 (vecNormSq_nonneg _ _)) h.A'_nonneg
  · intro k
    unfold smulLowConst
    refine mul_nonneg (mul_nonneg (add_nonneg hA3 (hB3 k)) ?_) ?_
    · exact add_nonneg (add_nonneg (vecNormSq_nonneg _ _) (vecNormSq_nonneg _ _))
        (vecNormSq_nonneg _ _)
    · have h1 := h.Bk_nonneg k
      have h2 := h.Bk_nonneg (k - 1)
      have h3 := h.Bk_nonneg r
      have h4 := h.A'_nonneg
      linarith
  · intro k hk v w hv hw α
    exact (third_multiplication_theorem_seq hn hr (by exact_mod_cast hk)
      (h.mem k hk v w hv hw) (ha k α)).1
  · intro k hk v w hv hw
    have hk1 : 1 ≤ k := le_trans (by exact_mod_cast hr1.le) hk
    have hcast : ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk1]; norm_num
    have hkR : ((r : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hvr : VMem n N (r : ℝ) v := hv.mono hkR
    have hwr : VMem n N (r : ℝ) w := hw.mono hkR
    have hQm : MemSobolev n (k : ℝ) (Q v w) := h.mem k hk v w hv hw
    have hQmr : MemSobolev n (r : ℝ) (Q v w) := h.mem r le_rfl v w hvr hwr
    have hlow0 : 0 ≤ lower n N r k v w := lower_nonneg r k v w
    have htop0 : 0 ≤ top n N r k v w := top_nonneg r k v w
    have hA'0 := h.A'_nonneg
    have hBkk := h.Bk_nonneg k
    have hBk1 := h.Bk_nonneg (k - 1)
    have hBr := h.Bk_nonneg r
    have hXlow : vecNormSq n N (r : ℝ) v * vecNormSq n N (r : ℝ) w ≤ lower n N r k v w := by
      have p1 : 0 ≤ vecNormSq n N ((k - 1 : ℕ) : ℝ) v * vecNormSq n N (r : ℝ) w :=
        mul_nonneg (vecNormSq_nonneg _ _) (vecNormSq_nonneg _ _)
      have p2 : 0 ≤ vecNormSq n N (r : ℝ) v * vecNormSq n N ((k - 1 : ℕ) : ℝ) w :=
        mul_nonneg (vecNormSq_nonneg _ _) (vecNormSq_nonneg _ _)
      unfold lower
      linarith
    have hQr : sobolevNormSq n (r : ℝ) (Q v w)
        ≤ (2 * A' + 3 * Bk r) * lower n N r k v w := by
      have hbr := h.bound r le_rfl v w hvr hwr
      have htr : top n N r r v w = 2 * (vecNormSq n N (r : ℝ) v * vecNormSq n N (r : ℝ) w) := by
        unfold top; ring
      have hlr : lower n N r r v w
          ≤ 3 * (vecNormSq n N (r : ℝ) v * vecNormSq n N (r : ℝ) w) := by
        have e1 : vecNormSq n N ((r - 1 : ℕ) : ℝ) v ≤ vecNormSq n N (r : ℝ) v :=
          vecNormSq_mono hvr (by exact_mod_cast Nat.sub_le r 1)
        have e2 : vecNormSq n N ((r - 1 : ℕ) : ℝ) w ≤ vecNormSq n N (r : ℝ) w :=
          vecNormSq_mono hwr (by exact_mod_cast Nat.sub_le r 1)
        have p1 := vecNormSq_nonneg (n := n) (N := N) (r : ℝ) v
        have p2 := vecNormSq_nonneg (n := n) (N := N) (r : ℝ) w
        unfold lower
        nlinarith
      rw [htr] at hbr
      have hstep : sobolevNormSq n (r : ℝ) (Q v w)
          ≤ (2 * A' + 3 * Bk r) * (vecNormSq n N (r : ℝ) v * vecNormSq n N (r : ℝ) w) := by
        nlinarith [mul_le_mul_of_nonneg_left hlr hBr]
      exact hstep.trans (mul_le_mul_of_nonneg_left hXlow (by linarith))
    have hQk1 : sobolevNormSq n ((k - 1 : ℕ) : ℝ) (Q v w)
        ≤ (Bk (k - 1) + 3 * A' + 3 * Bk r) * lower n N r k v w := by
      rcases eq_or_lt_of_le hk with heq | hlt
      · have hmono : sobolevNormSq n ((k - 1 : ℕ) : ℝ) (Q v w)
            ≤ sobolevNormSq n (r : ℝ) (Q v w) := by
          refine sobolevNormSq_mono hQmr ?_
          have : (k - 1 : ℕ) ≤ r := by omega
          exact_mod_cast this
        have hextra : 0 ≤ (Bk (k - 1) + A') * lower n N r k v w :=
          mul_nonneg (by linarith) hlow0
        nlinarith [hmono, hQr, hextra]
      · have hkr1 : r ≤ k - 1 := by omega
        have hsucc : k - 1 + 1 = k := by omega
        have hvk1 : VMem n N ((k - 1 : ℕ) : ℝ) v :=
          hv.mono (by exact_mod_cast Nat.sub_le k 1)
        have hwk1 : VMem n N ((k - 1 : ℕ) : ℝ) w :=
          hw.mono (by exact_mod_cast Nat.sub_le k 1)
        have hb1 := h.bound (k - 1) hkr1 v w hvk1 hwk1
        have htl : top n N r (k - 1) v w ≤ lower n N r k v w := by
          have ht := top_le_lower_succ (n := n) (N := N) r (k - 1) v w
          rwa [hsucc] at ht
        have hll : lower n N r (k - 1) v w ≤ lower n N r k v w := by
          have hv' : VMem n N ((k - 1 + 1 : ℕ) : ℝ) v := by rw [hsucc]; exact hv
          have hw' : VMem n N ((k - 1 + 1 : ℕ) : ℝ) w := by rw [hsucc]; exact hw
          have hl := lower_mono (n := n) (N := N) hkr1 hv' hw'
          rwa [hsucc] at hl
        nlinarith [mul_le_mul_of_nonneg_left htl hA'0, mul_le_mul_of_nonneg_left hll hBk1,
          mul_nonneg (show (0 : ℝ) ≤ 2 * A' + 3 * Bk r by linarith) hlow0]
    have hper : ∀ α : Fin N, sobolevNormSq n (k : ℝ) (seqConv (Q v w) (a α)) ≤
        mt3AConstSq n (r : ℝ) * (sobolevNormSq n (k : ℝ) (Q v w) * sobolevNormSq n (r : ℝ) (a α)
          + sobolevNormSq n (r : ℝ) (Q v w) * sobolevNormSq n (k : ℝ) (a α))
        + mt3BConstSq n k (r : ℝ) * (sobolevNormSq n ((k - 1 : ℕ) : ℝ) (Q v w)
            * sobolevNormSq n (r : ℝ) (a α)
          + sobolevNormSq n (r : ℝ) (Q v w) * sobolevNormSq n ((k - 1 : ℕ) : ℝ) (a α)) := by
      intro α
      have hmt := (third_multiplication_theorem_seq hn hr (by exact_mod_cast hk) hQm (ha k α)).2
      rw [hcast] at hmt
      exact hmt
    have hsum : vecNormSq n N (k : ℝ) (NashEmbedding.smulSeq (Q v w) a) ≤
        (mt3AConstSq n (r : ℝ) * sobolevNormSq n (k : ℝ) (Q v w)
          + mt3BConstSq n k (r : ℝ) * sobolevNormSq n ((k - 1 : ℕ) : ℝ) (Q v w))
            * vecNormSq n N (r : ℝ) a
        + (mt3AConstSq n (r : ℝ) * sobolevNormSq n (r : ℝ) (Q v w)) * vecNormSq n N (k : ℝ) a
        + (mt3BConstSq n k (r : ℝ) * sobolevNormSq n (r : ℝ) (Q v w))
            * vecNormSq n N ((k - 1 : ℕ) : ℝ) a := by
      have h1 : vecNormSq n N (k : ℝ) (NashEmbedding.smulSeq (Q v w) a)
          = ∑ α, sobolevNormSq n (k : ℝ) (seqConv (Q v w) (a α)) := rfl
      rw [h1]
      refine le_trans (Finset.sum_le_sum fun α _ => hper α) ?_
      simp only [vecNormSq, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun α _ => le_of_eq (by ring)
    have har := vecNormSq_nonneg (n := n) (N := N) (r : ℝ) a
    have hak := vecNormSq_nonneg (n := n) (N := N) (k : ℝ) a
    have hak1 := vecNormSq_nonneg (n := n) (N := N) ((k - 1 : ℕ) : ℝ) a
    have hB3k := hB3 k
    have hbk := h.bound k hk v w hv hw
    have e1 : mt3AConstSq n (r : ℝ) * vecNormSq n N (r : ℝ) a * sobolevNormSq n (k : ℝ) (Q v w)
        ≤ mt3AConstSq n (r : ℝ) * vecNormSq n N (r : ℝ) a
            * (A' * top n N r k v w + Bk k * lower n N r k v w) :=
      mul_le_mul_of_nonneg_left hbk (mul_nonneg hA3 har)
    have e2 : mt3BConstSq n k (r : ℝ) * vecNormSq n N (r : ℝ) a
          * sobolevNormSq n ((k - 1 : ℕ) : ℝ) (Q v w)
        ≤ mt3BConstSq n k (r : ℝ) * vecNormSq n N (r : ℝ) a
            * ((Bk (k - 1) + 3 * A' + 3 * Bk r) * lower n N r k v w) :=
      mul_le_mul_of_nonneg_left hQk1 (mul_nonneg hB3k har)
    have e3 : mt3AConstSq n (r : ℝ) * vecNormSq n N (k : ℝ) a * sobolevNormSq n (r : ℝ) (Q v w)
        ≤ mt3AConstSq n (r : ℝ) * vecNormSq n N (k : ℝ) a
            * ((2 * A' + 3 * Bk r) * lower n N r k v w) :=
      mul_le_mul_of_nonneg_left hQr (mul_nonneg hA3 hak)
    have e4 : mt3BConstSq n k (r : ℝ) * vecNormSq n N ((k - 1 : ℕ) : ℝ) a
          * sobolevNormSq n (r : ℝ) (Q v w)
        ≤ mt3BConstSq n k (r : ℝ) * vecNormSq n N ((k - 1 : ℕ) : ℝ) a
            * ((2 * A' + 3 * Bk r) * lower n N r k v w) :=
      mul_le_mul_of_nonneg_left hQr (mul_nonneg hB3k hak1)
    have hF1 : (0 : ℝ) ≤ (Bk k + Bk (k - 1) + 3 * A' + 3 * Bk r + 1) - Bk k := by linarith
    have hF2 : (0 : ℝ) ≤ (Bk k + Bk (k - 1) + 3 * A' + 3 * Bk r + 1)
        - (Bk (k - 1) + 3 * A' + 3 * Bk r) := by linarith
    have hF3 : (0 : ℝ) ≤ (Bk k + Bk (k - 1) + 3 * A' + 3 * Bk r + 1)
        - (2 * A' + 3 * Bk r) := by linarith
    have hF0 : (0 : ℝ) ≤ Bk k + Bk (k - 1) + 3 * A' + 3 * Bk r + 1 := by linarith
    have hP : 0 ≤ mt3AConstSq n (r : ℝ) * vecNormSq n N (r : ℝ) a := mul_nonneg hA3 har
    have hR : 0 ≤ mt3BConstSq n k (r : ℝ) * vecNormSq n N (r : ℝ) a := mul_nonneg hB3k har
    have hS : 0 ≤ mt3AConstSq n (r : ℝ) * vecNormSq n N (k : ℝ) a := mul_nonneg hA3 hak
    have hT : 0 ≤ mt3BConstSq n k (r : ℝ) * vecNormSq n N ((k - 1 : ℕ) : ℝ) a :=
      mul_nonneg hB3k hak1
    have hU : 0 ≤ mt3AConstSq n (r : ℝ) * vecNormSq n N ((k - 1 : ℕ) : ℝ) a :=
      mul_nonneg hA3 hak1
    have hV : 0 ≤ mt3BConstSq n k (r : ℝ) * vecNormSq n N (k : ℝ) a := mul_nonneg hB3k hak
    have hbracket :
        (mt3AConstSq n (r : ℝ) * vecNormSq n N (r : ℝ) a) * Bk k
          + (mt3BConstSq n k (r : ℝ) * vecNormSq n N (r : ℝ) a)
              * (Bk (k - 1) + 3 * A' + 3 * Bk r)
          + (mt3AConstSq n (r : ℝ) * vecNormSq n N (k : ℝ) a) * (2 * A' + 3 * Bk r)
          + (mt3BConstSq n k (r : ℝ) * vecNormSq n N ((k - 1 : ℕ) : ℝ) a)
              * (2 * A' + 3 * Bk r)
        ≤ smulLowConst n N r a A' Bk k := by
      unfold smulLowConst
      linarith only [mul_nonneg hP hF1, mul_nonneg hR hF2, mul_nonneg hS hF3, mul_nonneg hT hF3,
        mul_nonneg hU hF0, mul_nonneg hV hF0]
    have hfinal := mul_le_mul_of_nonneg_right hbracket hlow0
    change vecNormSq n N (k : ℝ) (NashEmbedding.smulSeq (Q v w) a) ≤ _
    unfold smulTopConst
    linarith only [hsum, e1, e2, e3, e4, hfinal]
  · intro v v' w hv hv' hw
    have hQ := h.sub_left v v' w hv hv' hw
    funext α
    change seqConv (Q (v - v') w) (a α) = _
    rw [hQ, seqConv_sub_left (s := (r : ℝ)) hn h2r (h.mem r le_rfl v w hv hw)
      (h.mem r le_rfl v' w hv' hw) (ha r α)]
    rfl
  · intro v w w' hv hw hw'
    have hQ := h.sub_right v w w' hv hw hw'
    funext α
    change seqConv (Q v (w - w')) (a α) = _
    rw [hQ, seqConv_sub_left (s := (r : ℝ)) hn h2r (h.mem r le_rfl v w hv hw)
      (h.mem r le_rfl v w' hv hw') (ha r α)]
    rfl

/-! ### The base case: `R (D₁ v · D₂ w)` -/

/-- Top constant of `R(D₁v · D₂w)`: `N · mt3AConstSq n (r - 2)`. -/
def baseTopConst (n N r : ℕ) : ℝ := N * mt3AConstSq n ((r : ℝ) - 2)

/-- Lower constant of `R(D₁v · D₂w)` at level `k`: `N · mt3BConstSq n (k - 2) (r - 2)`. -/
def baseLowConst (n N r : ℕ) (k : ℕ) : ℝ := N * mt3BConstSq n (k - 2) ((r : ℝ) - 2)

/-- **The base tame estimate.** For derivative operators `D₁, D₂` of orders `d₁, d₂ ≤ 2`,
`Q v w := R (D₁ v · D₂ w)` is tame at base level `r` whenever `1 + n/2 < r - 2`.
Proof: `‖R x‖²_(k) = ‖x‖²_(k-2)`, then MT3 at level `k - 2` with `r' = r - 2` on each of the
`N` products, `‖∑ α, xα‖² ≤ N ∑ ‖xα‖²`, and `‖Dᵢ v‖²_(s) ≤ ‖v‖²_(s + dᵢ) ≤ ‖v‖²_(s+2)`. -/
theorem scalarTame_resolvent_dotConv (hn : 0 < n) {r : ℕ} (hr : 1 + (n : ℝ) / 2 < (r : ℝ) - 2)
    {D₁ D₂ : VecSeq n N → VecSeq n N} {d₁ d₂ : ℕ} (h₁ : IsDerivOp D₁ d₁) (h₂ : IsDerivOp D₂ d₂)
    (hd₁ : d₁ ≤ 2) (hd₂ : d₂ ≤ 2) :
    ScalarTame n N r (fun v w => resolventCoeff (dotConv (D₁ v) (D₂ w)))
      (baseTopConst n N r) (baseLowConst n N r) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrR : (3 : ℝ) < (r : ℝ) := by linarith
  have hr4 : 4 ≤ r := by
    have h3 : 3 < r := by exact_mod_cast hrR
    omega
  have hd1R : (d₁ : ℝ) ≤ 2 := by exact_mod_cast hd₁
  have hd2R : (d₂ : ℝ) ≤ 2 := by exact_mod_cast hd₂
  have hs2r : (n : ℝ) < 2 * ((r : ℝ) - 2) := by linarith
  have hA3 : 0 ≤ mt3AConstSq n ((r : ℝ) - 2) := by
    have h0 : (0 : ℝ) ≤ mt3KSq n ((r : ℝ) - 2) := by
      unfold mt3KSq; exact tsum_nonneg fun j => weight_nonneg _ _
    unfold mt3AConstSq; linarith
  have hB3 : ∀ j : ℕ, 0 ≤ mt3BConstSq n j ((r : ℝ) - 2) := by
    intro j
    have hL : (0 : ℝ) ≤ mt3LSq n ((r : ℝ) - 2) := by
      unfold mt3LSq; exact tsum_nonneg fun i => weight_nonneg _ _
    have hS : 0 ≤ mt3BStar j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · norm_num [mt3BStar]
      · exact mt3BStar_nonneg hj
    unfold mt3BConstSq
    exact mul_nonneg (mul_nonneg (by norm_num) hS) hL
  have hprod : ∀ f g : Fin N → ℝ, (∀ α, 0 ≤ f α) → (∀ α, 0 ≤ g α) →
      ∑ α, f α * g α ≤ (∑ α, f α) * (∑ α, g α) := by
    intro f g hf hg
    rw [Finset.sum_mul_sum]
    exact Finset.sum_le_sum fun α _ =>
      Finset.single_le_sum (f := fun β => f α * g β)
        (fun β _ => mul_nonneg (hf α) (hg β)) (Finset.mem_univ α)
  have key : ∀ k : ℕ, r ≤ k → ∀ v w : VecSeq n N, VMem n N k v → VMem n N k w →
      MemSobolev n (k : ℝ) (resolventCoeff (dotConv (D₁ v) (D₂ w)))
      ∧ sobolevNormSq n (k : ℝ) (resolventCoeff (dotConv (D₁ v) (D₂ w)))
          ≤ baseTopConst n N r * top n N r k v w
            + baseLowConst n N r k * lower n N r k v w := by
    intro k hk v w hv hw
    have hk4 : 4 ≤ k := le_trans hr4 hk
    have hkR : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hs : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
      have h2 : (2 : ℕ) ≤ k := by omega
      rw [Nat.cast_sub h2]; norm_num
    have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ k := by omega
      rw [Nat.cast_sub h1]; norm_num
    have hvk1 : VMem n N ((k - 1 : ℕ) : ℝ) v := hv.mono (by rw [hkm1]; linarith)
    have hwk1 : VMem n N ((k - 1 : ℕ) : ℝ) w := hw.mono (by rw [hkm1]; linarith)
    have hvr : VMem n N (r : ℝ) v := hv.mono hkR
    have hwr : VMem n N (r : ℝ) w := hw.mono hkR
    -- level `k - 2`
    have hv_j : VMem n N (((k - 2 : ℕ) : ℝ) + (d₁ : ℝ)) v := hv.mono (by rw [hs]; linarith)
    have hw_j : VMem n N (((k - 2 : ℕ) : ℝ) + (d₂ : ℝ)) w := hw.mono (by rw [hs]; linarith)
    have hD1j : VMem n N ((k - 2 : ℕ) : ℝ) (D₁ v) := h₁.mem _ v hv_j
    have hD2j : VMem n N ((k - 2 : ℕ) : ℝ) (D₂ w) := h₂.mem _ w hw_j
    have nD1j : vecNormSq n N ((k - 2 : ℕ) : ℝ) (D₁ v) ≤ vecNormSq n N (k : ℝ) v :=
      le_trans (h₁.bound _ v hv_j) (vecNormSq_mono hv (by rw [hs]; linarith))
    have nD2j : vecNormSq n N ((k - 2 : ℕ) : ℝ) (D₂ w) ≤ vecNormSq n N (k : ℝ) w :=
      le_trans (h₂.bound _ w hw_j) (vecNormSq_mono hw (by rw [hs]; linarith))
    -- level `r - 2`
    have hv_r2 : VMem n N (((r : ℝ) - 2) + (d₁ : ℝ)) v := hv.mono (by linarith)
    have hw_r2 : VMem n N (((r : ℝ) - 2) + (d₂ : ℝ)) w := hw.mono (by linarith)
    have nD1r2 : vecNormSq n N ((r : ℝ) - 2) (D₁ v) ≤ vecNormSq n N (r : ℝ) v :=
      le_trans (h₁.bound _ v hv_r2) (vecNormSq_mono hvr (by linarith))
    have nD2r2 : vecNormSq n N ((r : ℝ) - 2) (D₂ w) ≤ vecNormSq n N (r : ℝ) w :=
      le_trans (h₂.bound _ w hw_r2) (vecNormSq_mono hwr (by linarith))
    -- level `k - 3`
    have hv_s1 : VMem n N ((((k - 2 : ℕ) : ℝ) - 1) + (d₁ : ℝ)) v :=
      hv.mono (by rw [hs]; linarith)
    have hw_s1 : VMem n N ((((k - 2 : ℕ) : ℝ) - 1) + (d₂ : ℝ)) w :=
      hw.mono (by rw [hs]; linarith)
    have nD1s1 : vecNormSq n N (((k - 2 : ℕ) : ℝ) - 1) (D₁ v)
        ≤ vecNormSq n N ((k - 1 : ℕ) : ℝ) v :=
      le_trans (h₁.bound _ v hv_s1) (vecNormSq_mono hvk1 (by rw [hs, hkm1]; linarith))
    have nD2s1 : vecNormSq n N (((k - 2 : ℕ) : ℝ) - 1) (D₂ w)
        ≤ vecNormSq n N ((k - 1 : ℕ) : ℝ) w :=
      le_trans (h₂.bound _ w hw_s1) (vecNormSq_mono hwk1 (by rw [hs, hkm1]; linarith))
    -- the multiplication theorem, componentwise
    have hkr2 : (r : ℝ) - 2 ≤ ((k - 2 : ℕ) : ℝ) := by rw [hs]; linarith
    have mt : ∀ α : Fin N,
        MemSobolev n ((k - 2 : ℕ) : ℝ) (seqConv (D₁ v α) (D₂ w α))
        ∧ sobolevNormSq n ((k - 2 : ℕ) : ℝ) (seqConv (D₁ v α) (D₂ w α))
            ≤ mt3AConstSq n ((r : ℝ) - 2)
                * (sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₁ v α)
                    * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α)
                  + sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                    * sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₂ w α))
              + mt3BConstSq n (k - 2) ((r : ℝ) - 2)
                * (sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₁ v α)
                    * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α)
                  + sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                    * sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₂ w α)) := fun α =>
      third_multiplication_theorem_seq hn hr hkr2 (hD1j α) (hD2j α)
    have hdot_mem : MemSobolev n ((k - 2 : ℕ) : ℝ) (dotConv (D₁ v) (D₂ w)) :=
      MemSobolev.finset_sum (n := n) (s := ((k - 2 : ℕ) : ℝ)) (Finset.univ : Finset (Fin N))
        (a := fun α => seqConv (D₁ v α) (D₂ w α)) (fun α _ => (mt α).1)
    have hj2 : ((k - 2 : ℕ) : ℝ) + 2 = (k : ℝ) := by rw [hs]; ring
    have hres_mem : MemSobolev n (k : ℝ) (resolventCoeff (dotConv (D₁ v) (D₂ w))) := by
      have hm := memSobolev_resolventCoeff hdot_mem
      rwa [hj2] at hm
    refine ⟨hres_mem, ?_⟩
    have hres_norm : sobolevNormSq n (k : ℝ) (resolventCoeff (dotConv (D₁ v) (D₂ w)))
        = sobolevNormSq n ((k - 2 : ℕ) : ℝ) (dotConv (D₁ v) (D₂ w)) := by
      rw [← hj2]
      exact sobolevNormSq_resolventCoeff _ _
    have hcard : ((Finset.univ : Finset (Fin N)).card : ℝ) = (N : ℝ) := by simp
    have hsum1 : sobolevNormSq n ((k - 2 : ℕ) : ℝ) (dotConv (D₁ v) (D₂ w))
        ≤ (N : ℝ) * ∑ α, sobolevNormSq n ((k - 2 : ℕ) : ℝ) (seqConv (D₁ v α) (D₂ w α)) := by
      have hle := sobolevNormSq_finset_sum_le (n := n) (s := ((k - 2 : ℕ) : ℝ))
        (Finset.univ : Finset (Fin N)) (a := fun α => seqConv (D₁ v α) (D₂ w α))
        (fun α _ => (mt α).1)
      rwa [hcard] at hle
    have hsum2 : ∑ α, sobolevNormSq n ((k - 2 : ℕ) : ℝ) (seqConv (D₁ v α) (D₂ w α))
        ≤ mt3AConstSq n ((r : ℝ) - 2) * top n N r k v w
          + mt3BConstSq n (k - 2) ((r : ℝ) - 2) * lower n N r k v w := by
      have step1 : ∑ α, sobolevNormSq n ((k - 2 : ℕ) : ℝ) (seqConv (D₁ v α) (D₂ w α))
          ≤ ∑ α, (mt3AConstSq n ((r : ℝ) - 2)
                * (sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₁ v α)
                    * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α)
                  + sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                    * sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₂ w α))
              + mt3BConstSq n (k - 2) ((r : ℝ) - 2)
                * (sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₁ v α)
                    * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α)
                  + sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                    * sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₂ w α))) :=
        Finset.sum_le_sum fun α _ => (mt α).2
      have step2 : ∑ α, (mt3AConstSq n ((r : ℝ) - 2)
                * (sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₁ v α)
                    * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α)
                  + sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                    * sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₂ w α))
              + mt3BConstSq n (k - 2) ((r : ℝ) - 2)
                * (sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₁ v α)
                    * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α)
                  + sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                    * sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₂ w α)))
          = mt3AConstSq n ((r : ℝ) - 2)
              * ((∑ α, sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₁ v α)
                    * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α))
                + ∑ α, sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                    * sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₂ w α))
            + mt3BConstSq n (k - 2) ((r : ℝ) - 2)
              * ((∑ α, sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₁ v α)
                    * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α))
                + ∑ α, sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                    * sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₂ w α)) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      have p12 : (∑ α, sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₁ v α)
            * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α))
          ≤ vecNormSq n N (k : ℝ) v * vecNormSq n N (r : ℝ) w :=
        le_trans (hprod _ _ (fun α => sobolevNormSq_nonneg _ _) (fun α => sobolevNormSq_nonneg _ _))
          (mul_le_mul nD1j nD2r2 (vecNormSq_nonneg _ _) (vecNormSq_nonneg _ _))
      have p34 : (∑ α, sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
            * sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₂ w α))
          ≤ vecNormSq n N (r : ℝ) v * vecNormSq n N (k : ℝ) w :=
        le_trans (hprod _ _ (fun α => sobolevNormSq_nonneg _ _) (fun α => sobolevNormSq_nonneg _ _))
          (mul_le_mul nD1r2 nD2j (vecNormSq_nonneg _ _) (vecNormSq_nonneg _ _))
      have p52 : (∑ α, sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₁ v α)
            * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α))
          ≤ vecNormSq n N ((k - 1 : ℕ) : ℝ) v * vecNormSq n N (r : ℝ) w :=
        le_trans (hprod _ _ (fun α => sobolevNormSq_nonneg _ _) (fun α => sobolevNormSq_nonneg _ _))
          (mul_le_mul nD1s1 nD2r2 (vecNormSq_nonneg _ _) (vecNormSq_nonneg _ _))
      have p36 : (∑ α, sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
            * sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₂ w α))
          ≤ vecNormSq n N (r : ℝ) v * vecNormSq n N ((k - 1 : ℕ) : ℝ) w :=
        le_trans (hprod _ _ (fun α => sobolevNormSq_nonneg _ _) (fun α => sobolevNormSq_nonneg _ _))
          (mul_le_mul nD1r2 nD2s1 (vecNormSq_nonneg _ _) (vecNormSq_nonneg _ _))
      have hA : mt3AConstSq n ((r : ℝ) - 2)
            * ((∑ α, sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₁ v α)
                  * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α))
              + ∑ α, sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                  * sobolevNormSq n ((k - 2 : ℕ) : ℝ) (D₂ w α))
          ≤ mt3AConstSq n ((r : ℝ) - 2) * top n N r k v w := by
        refine mul_le_mul_of_nonneg_left ?_ hA3
        unfold top
        linarith
      have hBb : mt3BConstSq n (k - 2) ((r : ℝ) - 2)
            * ((∑ α, sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₁ v α)
                  * sobolevNormSq n ((r : ℝ) - 2) (D₂ w α))
              + ∑ α, sobolevNormSq n ((r : ℝ) - 2) (D₁ v α)
                  * sobolevNormSq n (((k - 2 : ℕ) : ℝ) - 1) (D₂ w α))
          ≤ mt3BConstSq n (k - 2) ((r : ℝ) - 2) * lower n N r k v w := by
        refine mul_le_mul_of_nonneg_left ?_ (hB3 (k - 2))
        have hnn : 0 ≤ vecNormSq n N (r : ℝ) v * vecNormSq n N (r : ℝ) w :=
          mul_nonneg (vecNormSq_nonneg _ _) (vecNormSq_nonneg _ _)
        unfold lower
        linarith
      linarith [step1, step2.le, step2.ge, hA, hBb]
    calc sobolevNormSq n (k : ℝ) (resolventCoeff (dotConv (D₁ v) (D₂ w)))
        = sobolevNormSq n ((k - 2 : ℕ) : ℝ) (dotConv (D₁ v) (D₂ w)) := hres_norm
      _ ≤ (N : ℝ) * ∑ α, sobolevNormSq n ((k - 2 : ℕ) : ℝ) (seqConv (D₁ v α) (D₂ w α)) := hsum1
      _ ≤ (N : ℝ) * (mt3AConstSq n ((r : ℝ) - 2) * top n N r k v w
            + mt3BConstSq n (k - 2) ((r : ℝ) - 2) * lower n N r k v w) :=
          mul_le_mul_of_nonneg_left hsum2 (Nat.cast_nonneg N)
      _ = baseTopConst n N r * top n N r k v w + baseLowConst n N r k * lower n N r k v w := by
          unfold baseTopConst baseLowConst; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold baseTopConst
    exact mul_nonneg (Nat.cast_nonneg N) hA3
  · intro k
    unfold baseLowConst
    exact mul_nonneg (Nat.cast_nonneg N) (hB3 (k - 2))
  · intro k hk v w hv hw
    exact (key k hk v w hv hw).1
  · intro k hk v w hv hw
    exact (key k hk v w hv hw).2
  · intro v v' w hv hv' hw
    have hD : D₁ (v - v') = D₁ v - D₁ v' := h₁.sub v v'
    have hm1 : VMem n N ((r : ℝ) - 2) (D₁ v) := h₁.mem _ v (hv.mono (by linarith))
    have hm1' : VMem n N ((r : ℝ) - 2) (D₁ v') := h₁.mem _ v' (hv'.mono (by linarith))
    have hm2 : VMem n N ((r : ℝ) - 2) (D₂ w) := h₂.mem _ w (hw.mono (by linarith))
    have hdot : dotConv (D₁ (v - v')) (D₂ w)
        = fun m => dotConv (D₁ v) (D₂ w) m - dotConv (D₁ v') (D₂ w) m := by
      funext m
      change ∑ α, seqConv ((D₁ (v - v')) α) (D₂ w α) m = _
      rw [hD]
      have hcv : ∀ α : Fin N, seqConv ((D₁ v - D₁ v') α) (D₂ w α)
          = fun m => seqConv (D₁ v α) (D₂ w α) m - seqConv (D₁ v' α) (D₂ w α) m := fun α =>
        seqConv_sub_left hn hs2r (hm1 α) (hm1' α) (hm2 α)
      simp only [hcv]
      rw [Finset.sum_sub_distrib]
      rfl
    funext m
    show resolventCoeff (dotConv (D₁ (v - v')) (D₂ w)) m = _
    rw [hdot]
    simp only [resolventCoeff, sub_div]
  · intro v w w' hv hw hw'
    have hD : D₂ (w - w') = D₂ w - D₂ w' := h₂.sub w w'
    have hm1 : VMem n N ((r : ℝ) - 2) (D₁ v) := h₁.mem _ v (hv.mono (by linarith))
    have hm2 : VMem n N ((r : ℝ) - 2) (D₂ w) := h₂.mem _ w (hw.mono (by linarith))
    have hm2' : VMem n N ((r : ℝ) - 2) (D₂ w') := h₂.mem _ w' (hw'.mono (by linarith))
    have hdot : dotConv (D₁ v) (D₂ (w - w'))
        = fun m => dotConv (D₁ v) (D₂ w) m - dotConv (D₁ v) (D₂ w') m := by
      funext m
      change ∑ α, seqConv (D₁ v α) ((D₂ (w - w')) α) m = _
      rw [hD]
      have hcv : ∀ α : Fin N, seqConv (D₁ v α) ((D₂ w - D₂ w') α)
          = fun m => seqConv (D₁ v α) (D₂ w α) m - seqConv (D₁ v α) (D₂ w' α) m := fun α =>
        seqConv_sub_right hn hs2r (hm1 α) (hm2 α) (hm2' α)
      simp only [hcv]
      rw [Finset.sum_sub_distrib]
      rfl
    funext m
    show resolventCoeff (dotConv (D₁ v) (D₂ (w - w'))) m = _
    rw [hdot]
    simp only [resolventCoeff, sub_div]

/-! ## The Günther operator -/

/-- Polarized `Fᵢ`: `Fb i v w = -R(Lv · ∂ᵢw)`. -/
def Fb (i : Fin n) (v w : VecSeq n N) : Seq n :=
  fun m => -(resolventCoeff (dotConv (vlap v) (vpartial i w)) m)

/-- Polarized `Uᵢⱼ`:
`Ub i j v w = R(∂ᵢv · ∂ⱼw) + 2 R(Lv · ∂ᵢ∂ⱼw) - 2 R(∑ₖ ∂ᵢ∂ₖv · ∂ⱼ∂ₖw)`. -/
def Ub (i j : Fin n) (v w : VecSeq n N) : Seq n :=
  fun m => resolventCoeff (dotConv (vpartial i v) (vpartial j w)) m
    + (2 : ℂ) * resolventCoeff (dotConv (vlap v) (vpartial i (vpartial j w))) m
    - (2 : ℂ) * ∑ k, resolventCoeff (dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k
        w))) m

/-- The index set of the second-derivative frame: pairs `p ≤ q`. -/
def pairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun pq => pq.1 ≤ pq.2

/-- The data of the Günther operator on the momentum side: the dual frame `a i`, `b p q`
(only `p ≤ q` is used) and the metric perturbation `h p q`, all as coefficient sequences. -/
structure GuntherData (n N : ℕ) where
  /-- Fourier coefficients of the dual fields for the first derivatives. -/
  a : Fin n → VecSeq n N
  /-- Fourier coefficients of the dual fields for the second derivatives. -/
  b : Fin n → Fin n → VecSeq n N
  /-- Fourier coefficients of the prescribed metric perturbation. -/
  h : Fin n → Fin n → Seq n

/-- The bilinear part: `B v w = -∑ᵢ Fb i v w · aᵢ + ∑_{p≤q} ½ Ub p q v w · b_{pq}`. -/
def gB (d : GuntherData n N) (v w : VecSeq n N) : VecSeq n N :=
  -(∑ i, smulSeq (Fb i v w) (d.a i))
    + ∑ pq ∈ pairs n, smulSeq (fun m => (1 / 2 : ℂ) * Ub pq.1 pq.2 v w m) (d.b pq.1 pq.2)

/-- The constant part: `c = -∑_{p≤q} ½ h_{pq} · b_{pq}`. -/
def gC (d : GuntherData n N) : VecSeq n N :=
  -(∑ pq ∈ pairs n, smulSeq (fun m => (1 / 2 : ℂ) * d.h pq.1 pq.2 m) (d.b pq.1 pq.2))

/-- `T v = c + B v v`. -/
def gT (d : GuntherData n N) (v : VecSeq n N) : VecSeq n N := gC d + gB d v v

/-- Regularity of the data: all frame and perturbation sequences lie in every `H^k`. -/
structure GuntherData.Smooth (d : GuntherData n N) : Prop where
  a_mem : ∀ i, ∀ k : ℕ, VMem n N k (d.a i)
  b_mem : ∀ p q, ∀ k : ℕ, VMem n N k (d.b p q)
  h_mem : ∀ p q, ∀ k : ℕ, MemSobolev n k (d.h p q)

/-- Tame constants of `Fb i`. -/
def FbTop (n N r : ℕ) : ℝ := baseTopConst n N r
/-- Lower-order tame constant for the bilinear term `Fb` at Sobolev level `k`. -/
def FbLow (n N r : ℕ) (k : ℕ) : ℝ := baseLowConst n N r k

theorem scalarTame_Fb (hn : 0 < n) {r : ℕ} (hr : 1 + (n : ℝ) / 2 < (r : ℝ) - 2) (i : Fin n) :
    ScalarTame n N r (Fb i) (FbTop n N r) (FbLow n N r) := by
  exact (scalarTame_resolvent_dotConv (N := N) hn hr isDerivOp_vlap (isDerivOp_vpartial i)
    le_rfl (by norm_num)).neg

/-- Tame constants of `Ub i j` (generous). -/
def UbTop (n N r : ℕ) : ℝ := 2 * (2 * (baseTopConst n N r + 4 * baseTopConst n N r)
  + 4 * (n * (n * baseTopConst n N r)))
/-- Lower-order tame constant for the bilinear term `Ub` at Sobolev level `k`. -/
def UbLow (n N r : ℕ) (k : ℕ) : ℝ := 2 * (2 * (baseLowConst n N r k + 4 * baseLowConst n N r k)
  + 4 * (n * (n * baseLowConst n N r k)))

theorem scalarTame_Ub (hn : 0 < n) {r : ℕ} (hr : 1 + (n : ℝ) / 2 < (r : ℝ) - 2) (i j : Fin n) :
    ScalarTame n N r (Ub i j) (UbTop n N r) (UbLow n N r) := by
  have h1 := scalarTame_resolvent_dotConv (N := N) hn hr (isDerivOp_vpartial i)
    (isDerivOp_vpartial j) (by norm_num) (by norm_num)
  have h2 := (scalarTame_resolvent_dotConv (N := N) hn hr isDerivOp_vlap
    (isDerivOp_vpartial_vpartial i j) le_rfl le_rfl).const_mul (2 : ℝ)
  have h3 := (ScalarTame.finset_sum (n := n) (N := N) (r := r) (Finset.univ : Finset (Fin n))
      (Q := fun p v w => resolventCoeff (dotConv (vpartial i (vpartial p v))
        (vpartial j (vpartial p w))))
      (A' := fun _ => baseTopConst n N r) (Bk := fun _ => baseLowConst n N r)
      (fun p _ => scalarTame_resolvent_dotConv hn hr (isDerivOp_vpartial_vpartial i p)
        (isDerivOp_vpartial_vpartial j p) le_rfl le_rfl)).const_mul (-2 : ℝ)
  have h := (h1.add h2).add h3
  have hfun : Ub i j = fun (v w : VecSeq n N) (m : Fin n → ℤ) =>
      (resolventCoeff (dotConv (vpartial i v) (vpartial j w)) m
        + ((2 : ℝ) : ℂ) * resolventCoeff (dotConv (vlap v) (vpartial i (vpartial j w))) m)
      + ((-2 : ℝ) : ℂ) * ∑ p, resolventCoeff (dotConv (vpartial i (vpartial p v))
          (vpartial j (vpartial p w))) m := by
    funext v w m
    unfold Ub
    push_cast
    ring
  have htop : UbTop n N r = 2 * (2 * (baseTopConst n N r + (2 : ℝ) ^ 2 * baseTopConst n N r)
      + (-2 : ℝ) ^ 2 * (((Finset.univ : Finset (Fin n)).card : ℝ)
        * ∑ _p : Fin n, baseTopConst n N r)) := by
    unfold UbTop
    simp [Finset.card_univ]
    ring
  have hlow : UbLow n N r = fun k =>
      2 * (2 * (baseLowConst n N r k + (2 : ℝ) ^ 2 * baseLowConst n N r k)
        + (-2 : ℝ) ^ 2 * (((Finset.univ : Finset (Fin n)).card : ℝ)
          * ∑ _p : Fin n, baseLowConst n N r k)) := by
    funext k
    unfold UbLow
    simp [Finset.card_univ]
    ring
  rw [hfun, htop, hlow]
  exact h

/-- Tame constants of `gB` (generous). -/
def gBTop (n N r : ℕ) (d : GuntherData n N) : ℝ :=
  2 * (n * ∑ i, smulTopConst n N r (d.a i) (FbTop n N r)
    + (pairs n).card * ∑ pq ∈ pairs n, smulTopConst n N r (d.b pq.1 pq.2) ((1 / 2) ^ 2 * UbTop n
        N r))
/-- Lower-order tame constant for the complete bilinear Günther operator. -/
def gBLow (n N r : ℕ) (d : GuntherData n N) (k : ℕ) : ℝ :=
  2 * (n * ∑ i, smulLowConst n N r (d.a i) (FbTop n N r) (FbLow n N r) k
    + (pairs n).card * ∑ pq ∈ pairs n,
        smulLowConst n N r (d.b pq.1 pq.2) ((1 / 2) ^ 2 * UbTop n N r) (fun k => (1 / 2) ^ 2 *
            UbLow n N r k) k)

theorem vecTame_gB (hn : 0 < n) {r : ℕ} (hr : 1 + (n : ℝ) / 2 < (r : ℝ) - 2)
    (d : GuntherData n N) (hd : d.Smooth) :
    VecTame n N r (gB d) (gBTop n N r d) (gBLow n N r d) := by
  have hr' : 1 + (n : ℝ) / 2 < r := by linarith
  have h1 := (VecTame.finset_sum (Finset.univ : Finset (Fin n))
    (Q := fun i v w => smulSeq (Fb i v w) (d.a i))
    (A' := fun i => smulTopConst n N r (d.a i) (FbTop n N r))
    (Bk := fun i => smulLowConst n N r (d.a i) (FbTop n N r) (FbLow n N r))
    (fun i _ => (scalarTame_Fb hn hr i).smulSeq hn hr' (d.a i) (hd.a_mem i))).neg
  have h2 := VecTame.finset_sum (pairs n)
    (Q := fun pq v w => smulSeq (fun m => ((1 / 2 : ℝ) : ℂ) * Ub pq.1 pq.2 v w m)
      (d.b pq.1 pq.2))
    (A' := fun pq => smulTopConst n N r (d.b pq.1 pq.2) ((1 / 2 : ℝ) ^ 2 * UbTop n N r))
    (Bk := fun pq => smulLowConst n N r (d.b pq.1 pq.2) ((1 / 2 : ℝ) ^ 2 * UbTop n N r)
      (fun k => (1 / 2 : ℝ) ^ 2 * UbLow n N r k))
    (fun pq _ => ((scalarTame_Ub hn hr pq.1 pq.2).const_mul (1 / 2 : ℝ)).smulSeq hn hr'
      (d.b pq.1 pq.2) (hd.b_mem pq.1 pq.2))
  have h := h1.add h2
  have hfun : gB d = fun (v w : VecSeq n N) =>
      -(∑ i, smulSeq (Fb i v w) (d.a i))
      + ∑ pq ∈ pairs n, smulSeq (fun m => ((1 / 2 : ℝ) : ℂ) * Ub pq.1 pq.2 v w m)
          (d.b pq.1 pq.2) := by
    funext v w
    unfold gB
    norm_num
  have htop : gBTop n N r d = 2 * (((Finset.univ : Finset (Fin n)).card : ℝ)
      * ∑ i, smulTopConst n N r (d.a i) (FbTop n N r)
      + ((pairs n).card : ℝ) * ∑ pq ∈ pairs n,
          smulTopConst n N r (d.b pq.1 pq.2) ((1 / 2 : ℝ) ^ 2 * UbTop n N r)) := by
    unfold gBTop
    simp
  have hlow : gBLow n N r d = fun k => 2 * (((Finset.univ : Finset (Fin n)).card : ℝ)
      * ∑ i, smulLowConst n N r (d.a i) (FbTop n N r) (FbLow n N r) k
      + ((pairs n).card : ℝ) * ∑ pq ∈ pairs n,
          smulLowConst n N r (d.b pq.1 pq.2) ((1 / 2 : ℝ) ^ 2 * UbTop n N r)
            (fun k => (1 / 2 : ℝ) ^ 2 * UbLow n N r k) k) := by
    funext k
    unfold gBLow
    simp
  rw [hfun, htop, hlow]
  exact h

lemma gC_mem (hn : 0 < n) {r : ℕ} (hr : 1 + (n : ℝ) / 2 < r) (d : GuntherData n N) (hd : d.Smooth) :
    ∀ k : ℕ, VMem n N k (gC d) := by
  intro k
  refine VMem.neg (VMem.finset_sum _ ?_)
  intro pq _ α
  have hkr : ((k : ℝ)) ≤ ((max k r : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_left k r
  have hrs : ((r : ℝ)) ≤ ((max k r : ℕ) : ℝ) := by exact_mod_cast Nat.le_max_right k r
  have hs : (n : ℝ) < 2 * ((max k r : ℕ) : ℝ) := by linarith
  have hf : MemSobolev n ((max k r : ℕ) : ℝ) (fun m => (1 / 2 : ℂ) * d.h pq.1 pq.2 m) :=
    (hd.h_mem pq.1 pq.2 (max k r)).smul _
  have hb : MemSobolev n ((max k r : ℕ) : ℝ) (d.b pq.1 pq.2 α) := hd.b_mem pq.1 pq.2 (max k r) α
  exact ((second_multiplication_theorem_seq hn hs hf hb).1).mono hkr

/-- The `E1` constant derived from the tame estimate at level `r`:
`‖B v w‖²_(r) ≤ (2 A' + 3 Bᵣ) ‖v‖²_(r) ‖w‖²_(r)`. -/
def gA (n N r : ℕ) (d : GuntherData n N) : ℝ := 2 * gBTop n N r d + 3 * gBLow n N r d r

/-- **The Günther operator satisfies the hypotheses of the abstract iteration.** -/
theorem gunther_iterHyp (hn : 0 < n) {r : ℕ} (hr : 1 + (n : ℝ) / 2 < (r : ℝ) - 2)
    (d : GuntherData n N) (hd : d.Smooth) :
    IterHyp n N r (gC d) (gB d) (gA n N r d) (gBTop n N r d) (gBLow n N r d) := by
  have hB := vecTame_gB hn hr d hd
  have hr' : 1 + (n : ℝ) / 2 < r := by linarith
  refine
    { A_nonneg := ?_
      A'_nonneg := hB.A'_nonneg
      Bk_nonneg := hB.Bk_nonneg
      c_mem := gC_mem hn hr' d hd
      B_mem := hB.mem
      E1 := ?_
      E2 := ?_
      polar := ?_ }
  · have h1 := hB.A'_nonneg
    have h2 := hB.Bk_nonneg r
    unfold gA
    linarith
  · intro v w hv hw
    have hb := hB.bound r le_rfl v w hv hw
    have hBk := hB.Bk_nonneg r
    have hA' := hB.A'_nonneg
    have hvn := vecNormSq_nonneg (n := n) (N := N) (r : ℝ) v
    have hwn := vecNormSq_nonneg (n := n) (N := N) (r : ℝ) w
    have htop : top n N r r v w = 2 * (vecNormSq n N r v * vecNormSq n N r w) := by
      unfold top; ring
    have hlow : lower n N r r v w ≤ 3 * (vecNormSq n N r v * vecNormSq n N r w) := by
      have h1 : vecNormSq n N ((r - 1 : ℕ) : ℝ) v ≤ vecNormSq n N r v :=
        vecNormSq_mono hv (by exact_mod_cast Nat.sub_le r 1)
      have h2 : vecNormSq n N ((r - 1 : ℕ) : ℝ) w ≤ vecNormSq n N r w :=
        vecNormSq_mono hw (by exact_mod_cast Nat.sub_le r 1)
      unfold lower
      nlinarith
    have hlow' := mul_le_mul_of_nonneg_left hlow hBk
    rw [htop] at hb
    unfold gA
    nlinarith
  · intro k hk v w hv hw
    have hb := hB.bound k hk.le v w hv hw
    unfold top lower at hb
    exact hb
  · intro v w hv hw
    have h1 := hB.sub_left v w v hv hw hv
    have h2 := hB.sub_right w v w hw hv hw
    rw [h1, h2]
    abel

end NashEmbedding

end
