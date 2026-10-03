/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Arith.Local.Val

/-! The generic rank-one (Vandermonde) lemma, in Newton form.
For H = W + sum_c sum_{t<C c} gamma_{c,t} v(a_{c,t}) v(a_{c,t})^T, v(a)_i = a^i, with W and
all nodes p-integral, nodes in one class pairwise congruent mod p, v_p(gamma_{c,t}) >= w_{c,t}
and w_c nondecreasing in t:
  v_p(det H) >= sum_c sum_{k<C c} min(w_{c,k} + 2k, 0). -/

public section

open Zeta32.Arith.Local

-- adapted from dtq1997/li2-half-irrationality@d5d8206:Li2Unified/Modular/Base/DecayExpand.lean
-- and .../Li2Unified/Modular/Base/DecayRankOne.lean (generic Vandermonde rank-one bound,
-- Newton form).
-- New here: `rank_one_GV_rows`, the same bound after multiplying the rows by p-integral scalars
-- (the proof notes section 4, Lemma 5: "multiplying the last r_p rows by p makes W integral").

open Polynomial
open scoped BigOperators
namespace Zeta32.Outer
noncomputable section

theorem det_mul_expand {R : Type*} [CommRing R] {h : ℕ} {I : Type*} [Fintype I]
    (W : Matrix (Fin h) I R) (Cm : Matrix I (Fin h) R) :
    (W * Cm).det = ∑ f : Fin h → I,
      (∏ b, Cm (f b) b) * (Matrix.of fun a b => W a (f b)).det := by
  classical
  rw [Matrix.det_apply]
  have hs : ∀ σ : Equiv.Perm (Fin h), ∏ i, (W * Cm) (σ i) i =
      ∑ f : Fin h → I, ∏ i, (W (σ i) (f i) * Cm (f i) i) := by
    intro σ
    simp only [Matrix.mul_apply]
    exact Fintype.prod_sum (fun i k => W (σ i) k * Cm k i)
  simp_rw [hs, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  rw [Matrix.det_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib, mul_smul_comm, mul_comm]
  rfl

lemma det_cols_eq_zero {R : Type*} [CommRing R] {h : ℕ} {I : Type*}
    (W : Matrix (Fin h) I R) (f : Fin h → I) (hf : ¬ Function.Injective f) :
    (Matrix.of fun a b => W a (f b)).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
    by_contra hcon
    push Not at hcon
    exact hf fun i j h => hcon i j h
  exact Matrix.det_zero_of_column_eq hne fun k => by simp [hij]

/-! ## Newton coefficients over a node sequence -/

/-- Successive monic quotients along the Newton interpolation nodes. -/
def newtonTail (a : ℕ → ℚ) (f : ℚ[X]) : ℕ → ℚ[X]
  | 0 => f
  | k+1 => newtonTail a f k /ₘ (X - C (a k))

/-- Newton interpolation coefficient at the `k`th node. -/
def ncoef (a : ℕ → ℚ) (f : ℚ[X]) (k : ℕ) : ℚ := (newtonTail a f k).eval (a k)

/-- The `k`th Newton basis polynomial associated to the node sequence. -/
def Nb (a : ℕ → ℚ) (k : ℕ) : ℚ[X] := ∏ s ∈ Finset.range k, (X - C (a s))

theorem newton_nodes (a : ℕ → ℚ) (f : ℚ[X]) (K : ℕ) :
    f = ∑ k ∈ Finset.range K, C (ncoef a f k) * Nb a k + Nb a K * newtonTail a f K := by
  induction K with
  | zero => simp [Nb, newtonTail]
  | succ K ih =>
    have hstep : newtonTail a f K =
        C (ncoef a f K) + (X - C (a K)) * newtonTail a f (K+1) := by
      have h := modByMonic_add_div (newtonTail a f K) (X - C (a K))
      rw [modByMonic_X_sub_C_eq_C_eval] at h
      rw [newtonTail, ncoef]
      exact h.symm
    conv_lhs => rw [ih, hstep]
    rw [Finset.sum_range_succ, Nb, Nb, Finset.prod_range_succ]
    ring

lemma Nb_eval_eq_zero (a : ℕ → ℚ) {k t : ℕ} (htk : t < k) : (Nb a k).eval (a t) = 0 := by
  rw [Nb, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_range.mpr htk) (by simp)

theorem pow_eval_newton (a : ℕ → ℚ) (i : ℕ) {K t : ℕ} (ht : t < K) :
    (a t)^i = ∑ k ∈ Finset.range K, ncoef a (X^i) k * (Nb a k).eval (a t) := by
  have h := congrArg (eval (a t)) (newton_nodes a (X^i) K)
  rw [eval_pow, eval_X] at h
  rw [h, eval_add, eval_mul, Nb_eval_eq_zero a ht, zero_mul, add_zero, eval_finsetSum]
  simp

lemma newtonTail_GV (p : ℕ) [Fact p.Prime] (a : ℕ → ℚ) (ha : ∀ k, VG p (a k) 0)
    {f : ℚ[X]} (hf : GV p f 0) (k : ℕ) : GV p (newtonTail a f k) 0 := by
  induction k with
  | zero => exact hf
  | succ k ih => exact GV.divByMonic_X_sub_C ih (ha k)

lemma ncoef_VG (p : ℕ) [Fact p.Prime] (a : ℕ → ℚ) (ha : ∀ k, VG p (a k) 0)
    {f : ℚ[X]} (hf : GV p f 0) (k : ℕ) : VG p (ncoef a f k) 0 :=
  VG.eval (newtonTail_GV p a ha hf k) (ha k)

lemma X_pow_GV (p : ℕ) [Fact p.Prime] (i : ℕ) : GV p ((X : ℚ[X])^i) 0 := by
  simpa using (GV.X (p := p)).pow i

lemma Nb_eval_VG (p : ℕ) [Fact p.Prime] (a : ℕ → ℚ) {k t : ℕ}
    (hd : ∀ s < k, VG p (a t - a s) 1) : VG p ((Nb a k).eval (a t)) (k:ℚ) := by
  rw [Nb, eval_prod]
  have h := VG.prod (p := p) (Finset.range k) (f := fun s => (X - C (a s)).eval (a t))
    (r := fun _ => 1) (fun s hs => by simpa using hd s (Finset.mem_range.mp hs))
  simpa using h

/-! ## The double expansion bound -/

theorem det_mul_GV2 (p : ℕ) [Fact p.Prime] {h : ℕ} {I : Type*} [Fintype I]
    (W : Matrix (Fin h) I ℚ[X]) (Cm : Matrix I (Fin h) ℚ[X]) (ρ : I → ℚ) (τ : Fin h → ℚ)
    (hW : ∀ a i, GV p (W a i) 0) (hC : ∀ i b, GV p (Cm i b) (ρ i + τ b)) (Bd : ℚ)
    (hB : ∀ f : Fin h → I, Function.Injective f → Bd ≤ ∑ b, ρ (f b)) :
    GV p (W * Cm).det (Bd + ∑ b, τ b) := by
  classical
  rw [det_mul_expand]
  apply GV.sum
  intro f _
  by_cases hf : Function.Injective f
  · have hprod : GV p (∏ b, Cm (f b) b) (∑ b, (ρ (f b) + τ b)) := GV.prod _ fun b _ => hC (f b) b
    have hdet : GV p (Matrix.of fun a b => W a (f b)).det (∑ _a : Fin h, (0:ℚ) + ∑ _b : Fin h,
      (0:ℚ)) :=
      det_GV (p := p) _ (fun _ => 0) (fun _ => 0) fun a b => by simpa using hW a (f b)
    simp only [Finset.sum_const_zero, add_zero] at hdet
    refine (hprod.mul hdet).mono ?_
    rw [Finset.sum_add_distrib, add_zero]
    linarith [hB f hf]
  · rw [det_cols_eq_zero W f hf, mul_zero]
    exact GV.zero _

lemma sum_min_le_of_injective {h : ℕ} {I : Type*} [Fintype I] (ρ : I → ℚ)
    (g : Fin h → I) (hg : Function.Injective g) : ∑ i, min (ρ i) 0 ≤ ∑ b, ρ (g b) := by
  classical
  have h1 : ∑ b, min (ρ (g b)) 0 ≤ ∑ b, ρ (g b) := Finset.sum_le_sum fun b _ => min_le_left _ _
  have h2 : ∑ b, min (ρ (g b)) 0 = ∑ i ∈ Finset.univ.image g, min (ρ i) 0 := by
    rw [Finset.sum_image fun x _ y _ hxy => hg hxy]
  have h3 : ∑ i, min (ρ i) 0 ≤ ∑ i ∈ Finset.univ.image g, min (ρ i) 0 := by
    rw [← Finset.sum_sdiff (Finset.subset_univ (Finset.univ.image g))]
    have : ∑ i ∈ Finset.univ \ Finset.univ.image g, min (ρ i) 0 ≤ 0 :=
      Finset.sum_nonpos fun i _ => min_le_right _ _
    linarith
  linarith

theorem det_sandwich_GV (p : ℕ) [Fact p.Prime] {h : ℕ} {I : Type*} [Fintype I]
    (A : Matrix (Fin h) I ℚ[X]) (M : Matrix I I ℚ[X]) (B : Matrix I (Fin h) ℚ[X]) (ρ : I → ℚ)
    (hA : ∀ a i, GV p (A a i) 0) (hB : ∀ i b, GV p (B i b) 0)
    (hM : ∀ i j, GV p (M i j) (ρ i + ρ j)) :
    GV p (A * M * B).det (2 * ∑ i, min (ρ i) 0) := by
  classical
  rw [det_mul_expand]
  apply GV.sum
  intro f _
  by_cases hf : Function.Injective f
  · have hprod : GV p (∏ b, B (f b) b) 0 := by
      simpa using GV.prod (p := p) Finset.univ (f := fun b => B (f b) b) (r := fun _ => 0)
        fun b _ => hB (f b) b
    have hcols : (Matrix.of fun a b => (A * M) a (f b)) =
        A * Matrix.of (fun i b => M i (f b)) := by
      ext a b
      simp [Matrix.mul_apply]
    have hdet : GV p (Matrix.of fun a b => (A * M) a (f b)).det
        (∑ i, min (ρ i) 0 + ∑ b, ρ (f b)) := by
      rw [hcols]
      exact det_mul_GV2 p A _ ρ (fun b => ρ (f b)) hA (fun i b => hM i (f b)) _
        (fun g hg => sum_min_le_of_injective ρ g hg)
    refine (hprod.mul hdet).mono ?_
    have := sum_min_le_of_injective ρ f hf
    linarith
  · have : (Matrix.of fun a b => (A * M) a (f b)).det = 0 := det_cols_eq_zero (A * M) f hf
    rw [this, mul_zero]
    exact GV.zero _

/-! ## The class-wise rank-one lemma -/

section RankOne
variable {h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (Cc : κ → ℕ)
  (node : κ → ℕ → ℚ) (γ : κ → ℕ → ℚ[X])

/-- Indices for the original matrix block and the residue-class interpolation blocks. -/
abbrev RSlot (h : ℕ) (Cc : κ → ℕ) := Fin h ⊕ (Σ c, Fin (Cc c))

/-- The weighted Newton-basis Gram polynomial for a residue class. -/
def Gc (c : κ) (k l : ℕ) : ℚ[X] :=
  ∑ t ∈ Finset.range (Cc c), γ c t *
    C ((Nb (node c) k).eval (node c t) * (Nb (node c) l).eval (node c t))

/-- Left factor in the residue-class block decomposition of the Hankel matrix. -/
def rankA (W : Matrix (Fin h) (Fin h) ℚ[X]) : Matrix (Fin h) (RSlot h Cc) ℚ[X] := fun a i =>
  match i with
  | Sum.inl i => W a i
  | Sum.inr ⟨c, k⟩ => C (ncoef (node c) (X^(a:ℕ)) k)

/-- Middle block matrix in the residue-class Hankel decomposition. -/
def rankM : Matrix (RSlot h Cc) (RSlot h Cc) ℚ[X] := fun i j =>
  match i, j with
  | Sum.inl i, Sum.inl j => if i = j then 1 else 0
  | Sum.inr ⟨c, k⟩, Sum.inr ⟨c', l⟩ => if c = c' then Gc Cc node γ c k l else 0
  | _, _ => 0

/-- Right factor in the residue-class block decomposition of the Hankel matrix. -/
def rankB : Matrix (RSlot h Cc) (Fin h) ℚ[X] := fun i b =>
  match i with
  | Sum.inl i => if i = b then 1 else 0
  | Sum.inr ⟨c, l⟩ => C (ncoef (node c) (X^(b:ℕ)) l)

omit [Fintype κ] [DecidableEq κ] in
lemma class_block (c : κ) (a b : ℕ) :
    ∑ k : Fin (Cc c), ∑ l : Fin (Cc c), C (ncoef (node c) (X^a) k) * Gc Cc node γ c k l *
        C (ncoef (node c) (X^b) l) =
      ∑ t ∈ Finset.range (Cc c), γ c t * C ((node c t)^a * (node c t)^b) := by
  have e : ∀ t ∈ Finset.range (Cc c), γ c t * C ((node c t)^a * (node c t)^b) =
      ∑ k : Fin (Cc c), ∑ l : Fin (Cc c), C (ncoef (node c) (X^a) k) *
        (γ c t * C ((Nb (node c) k).eval (node c t) * (Nb (node c) l).eval (node c t))) *
        C (ncoef (node c) (X^b) l) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [pow_eval_newton (node c) a ht', pow_eval_newton (node c) b ht',
      ← Fin.sum_univ_eq_sum_range (fun k => ncoef (node c) (X^a) k * (Nb (node c) k).eval (node
        c t)),
      ← Fin.sum_univ_eq_sum_range (fun l => ncoef (node c) (X^b) l * (Nb (node c) l).eval (node
        c t)),
      Finset.sum_mul_sum, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    simp only [map_mul]
    ring
  rw [Finset.sum_congr rfl e]
  simp only [Gc, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_comm]

theorem rank_decomp (W : Matrix (Fin h) (Fin h) ℚ[X]) (a b : Fin h) :
    (rankA Cc node W * rankM (h := h) Cc node γ * rankB (h := h) Cc node) a b =
      W a b + ∑ c, ∑ t ∈ Finset.range (Cc c), γ c t * C ((node c t)^(a:ℕ) * (node c t)^(b:ℕ)) := by
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [rankA, rankM, rankB]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero, zero_add]
  congr 1
  apply Finset.sum_congr rfl; intro c _
  rw [← class_block Cc node γ c a b, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_mul, Finset.sum_eq_single c (fun c' _ hc' => by
    simp [hc']) (by simp)]
  simp only [ite_true, Finset.sum_mul]

variable (p : ℕ) [Fact p.Prime] (w : κ → ℕ → ℚ)

/-- Valuation weight on each original or interpolation matrix slot. -/
def rankρ : RSlot h Cc → ℚ
  | Sum.inl _ => 0
  | Sum.inr ⟨c, k⟩ => w c k / 2 + (k:ℚ)

omit [DecidableEq κ] in
theorem rank_one_GV (W : Matrix (Fin h) (Fin h) ℚ[X]) (hW : ∀ a b, GV p (W a b) 0)
    (hnode : ∀ c t, VG p (node c t) 0)
    (hsep : ∀ c s t, s < Cc c → t < Cc c → s ≠ t → VG p (node c t - node c s) 1)
    (hγ : ∀ c t, t < Cc c → GV p (γ c t) (w c t))
    (hmono : ∀ c s t, s ≤ t → t < Cc c → w c s ≤ w c t) :
    GV p (Matrix.of fun a b : Fin h =>
        W a b + ∑ c, ∑ t ∈ Finset.range (Cc c), γ c t * C ((node c t)^(a:ℕ) * (node c t)^(b:ℕ))).det
      (∑ c, ∑ k ∈ Finset.range (Cc c), min (w c k + 2 * k) 0) := by
  classical
  have hH : (Matrix.of fun a b : Fin h =>
      W a b + ∑ c, ∑ t ∈ Finset.range (Cc c), γ c t * C ((node c t)^(a:ℕ) * (node c t)^(b:ℕ))) =
      rankA Cc node W * rankM (h := h) Cc node γ * rankB (h := h) Cc node := by
    ext a b; rw [rank_decomp]; rfl
  have hsum : 2 * ∑ i, min (rankρ (h := h) Cc w i) 0 =
      ∑ c, ∑ k ∈ Finset.range (Cc c), min (w c k + 2 * k) 0 := by
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [rankρ, min_self, Finset.sum_const_zero, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    rw [← Fin.sum_univ_eq_sum_range (fun k => min (w c k + 2 * k) 0)]
    apply Finset.sum_congr rfl; intro k _
    rw [show w c k + 2 * (k:ℚ) = 2 * (w c k / 2 + k) by ring]
    rcases le_total (w c k / 2 + (k:ℚ)) 0 with hle | hle
    · rw [min_eq_left hle, min_eq_left (by linarith)]
    · rw [min_eq_right hle, min_eq_right (by linarith)]; ring
  rw [hH, ← hsum]
  apply det_sandwich_GV p _ _ _ (rankρ (h := h) Cc w)
  · intro a i
    rcases i with i | ⟨c, k⟩
    · exact hW a i
    · exact GV.C (ncoef_VG p _ (hnode c) (X_pow_GV p _) k)
  · intro i b
    rcases i with i | ⟨c, l⟩
    · simp only [rankB]; split_ifs
      · exact GV.C VG.one
      · exact GV.zero _
    · exact GV.C (ncoef_VG p _ (hnode c) (X_pow_GV p _) l)
  · intro i j
    rcases i with i | ⟨c, k⟩ <;> rcases j with j | ⟨c', l⟩
    · simp only [rankM, rankρ]; split_ifs
      · simpa using GV.C (VG.one (p := p))
      · exact GV.zero _
    · exact GV.zero _
    · exact GV.zero _
    · simp only [rankM, rankρ]
      split_ifs with hcc
      · subst hcc
        unfold Gc
        apply GV.sum
        intro t ht
        have ht' := Finset.mem_range.mp ht
        by_cases hkt : (k:ℕ) ≤ t ∧ (l:ℕ) ≤ t
        · have hk := Nb_eval_VG p (node c) (k := k) (t := t) fun s hs =>
            hsep c s t (by have := k.isLt; omega) ht' (by omega)
          have hl := Nb_eval_VG p (node c) (k := l) (t := t) fun s hs =>
            hsep c s t (by have := l.isLt; omega) ht' (by omega)
          refine ((hγ c t ht').mul (GV.C (hk.mul hl))).mono ?_
          have m1 := hmono c k t hkt.1 ht'
          have m2 := hmono c l t hkt.2 ht'
          linarith
        · have hz : (Nb (node c) k).eval (node c t) * (Nb (node c) l).eval (node c t) = 0 := by
            rcases not_and_or.mp hkt with h1 | h1
            · rw [Nb_eval_eq_zero _ (by omega), zero_mul]
            · rw [Nb_eval_eq_zero _ (by omega : t < (l:ℕ)), mul_zero]
          rw [hz, map_zero, mul_zero]
          exact GV.zero _
      · exact GV.zero _

end RankOne

section RowScaled
variable {h : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (Cc : κ → ℕ)
  (node : κ → ℕ → ℚ) (γ : κ → ℕ → ℚ[X])
variable (p : ℕ) [Fact p.Prime] (w : κ → ℕ → ℚ)

omit [DecidableEq κ] in
/-- Rank-one bound after scaling row `a` by a `p`-integral scalar `d a`; only the scaled `W` has
to be integral. -/
theorem rank_one_GV_rows (d : Fin h → ℚ) (hd : ∀ a, VG p (d a) 0)
    (W : Matrix (Fin h) (Fin h) ℚ[X]) (hW : ∀ a b, GV p (C (d a) * W a b) 0)
    (hnode : ∀ c t, VG p (node c t) 0)
    (hsep : ∀ c s t, s < Cc c → t < Cc c → s ≠ t → VG p (node c t - node c s) 1)
    (hγ : ∀ c t, t < Cc c → GV p (γ c t) (w c t))
    (hmono : ∀ c s t, s ≤ t → t < Cc c → w c s ≤ w c t) :
    GV p (Matrix.of fun a b : Fin h => C (d a) *
        (W a b + ∑ c, ∑ t ∈ Finset.range (Cc c), γ c t * C ((node c t)^(a:ℕ) * (node c
          t)^(b:ℕ)))).det
      (∑ c, ∑ k ∈ Finset.range (Cc c), min (w c k + 2 * k) 0) := by
  classical
  have hH : (Matrix.of fun a b : Fin h => C (d a) *
      (W a b + ∑ c, ∑ t ∈ Finset.range (Cc c), γ c t * C ((node c t)^(a:ℕ) * (node c t)^(b:ℕ)))) =
      (Matrix.diagonal (fun a => C (d a)) * rankA Cc node W) * rankM (h := h) Cc node γ *
        rankB (h := h) Cc node := by
    ext a b
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.diagonal_mul, ← Matrix.mul_assoc, rank_decomp]
    rfl
  have hsum : 2 * ∑ i, min (rankρ (h := h) Cc w i) 0 =
      ∑ c, ∑ k ∈ Finset.range (Cc c), min (w c k + 2 * k) 0 := by
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [rankρ, min_self, Finset.sum_const_zero, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    rw [← Fin.sum_univ_eq_sum_range (fun k => min (w c k + 2 * k) 0)]
    apply Finset.sum_congr rfl; intro k _
    rw [show w c k + 2 * (k:ℚ) = 2 * (w c k / 2 + k) by ring]
    rcases le_total (w c k / 2 + (k:ℚ)) 0 with hle | hle
    · rw [min_eq_left hle, min_eq_left (by linarith)]
    · rw [min_eq_right hle, min_eq_right (by linarith)]; ring
  rw [hH, ← hsum]
  apply det_sandwich_GV p _ _ _ (rankρ (h := h) Cc w)
  · intro a i
    rw [Matrix.diagonal_mul]
    rcases i with i | ⟨c, k⟩
    · exact hW a i
    · have := GV.C (p := p) ((hd a).mul (ncoef_VG p _ (hnode c) (X_pow_GV p (a:ℕ)) k))
      simpa [rankA, C_mul] using this
  · intro i b
    rcases i with i | ⟨c, l⟩
    · simp only [rankB]; split_ifs
      · exact GV.C VG.one
      · exact GV.zero _
    · exact GV.C (ncoef_VG p _ (hnode c) (X_pow_GV p _) l)
  · intro i j
    rcases i with i | ⟨c, k⟩ <;> rcases j with j | ⟨c', l⟩
    · simp only [rankM, rankρ]; split_ifs
      · simpa using GV.C (VG.one (p := p))
      · exact GV.zero _
    · exact GV.zero _
    · exact GV.zero _
    · simp only [rankM, rankρ]
      split_ifs with hcc
      · subst hcc
        unfold Gc
        apply GV.sum
        intro t ht
        have ht' := Finset.mem_range.mp ht
        by_cases hkt : (k:ℕ) ≤ t ∧ (l:ℕ) ≤ t
        · have hk := Nb_eval_VG p (node c) (k := k) (t := t) fun s hs =>
            hsep c s t (by have := k.isLt; omega) ht' (by omega)
          have hl := Nb_eval_VG p (node c) (k := l) (t := t) fun s hs =>
            hsep c s t (by have := l.isLt; omega) ht' (by omega)
          refine ((hγ c t ht').mul (GV.C (hk.mul hl))).mono ?_
          have m1 := hmono c k t hkt.1 ht'
          have m2 := hmono c l t hkt.2 ht'
          linarith
        · have hz : (Nb (node c) k).eval (node c t) * (Nb (node c) l).eval (node c t) = 0 := by
            rcases not_and_or.mp hkt with h1 | h1
            · rw [Nb_eval_eq_zero _ (by omega), zero_mul]
            · rw [Nb_eval_eq_zero _ (by omega : t < (l:ℕ)), mul_zero]
          rw [hz, map_zero, mul_zero]
          exact GV.zero _
      · exact GV.zero _

end RowScaled

end
end Zeta32.Outer

end
