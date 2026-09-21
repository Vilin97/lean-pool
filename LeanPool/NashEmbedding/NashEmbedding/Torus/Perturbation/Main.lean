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
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.DualFrame
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.GuntherIdentitySeq

/-!
# Theorem B (Günther's perturbation theorem) for the flat torus

Let `u₀ : ℝⁿ → ℝᴺ` be smooth, `2πℤⁿ`-periodic and *free*: at every point the
`n + n(n+1)/2` vectors `∂ᵢu₀`, `∂ₚ∂_q u₀` (`p ≤ q`) are linearly independent. Then there is
`ε > 0` such that for every smooth periodic symmetric `h` with `H^r` size `< ε`
(`r = ⌊n/2⌋ + 4`) there is a smooth periodic `v : ℝⁿ → ℝᴺ` with

  `∂ᵢ(u₀ + v) · ∂ⱼ(u₀ + v) = ∂ᵢu₀ · ∂ⱼu₀ + hᵢⱼ`.

Proof shape:
1. the dual frame `D` of `{∂ᵢu₀} ∪ {∂ₚ∂_q u₀}` (`DualFrame.lean`);
2. the Günther operator `T v = c + B v v` on coefficient sequences, built from the
   coefficients of `D` and `h` (`GuntherOperator.lean`), satisfies `IterHyp`;
3. the abstract iteration (`GuntherIteration.lean`) gives a fixed point `v∞` in every `H^k`,
   with `conjReflect`-fixed (real) components, when `4 ‖c‖²_(r) ≤ ρ`, i.e. when `h` is small;
4. the synthesis `V = vsynth v∞` is smooth periodic, and taking coefficients of the
   position-space expression `-∑ᵢ F_tildeᵢ Dᵢ + ∑_{p≤q} ½(U_tilde_{pq} - h_{pq}) D_{pq}` shows
     `V` equals it;
5. the dual-frame relations turn this into the ansatz `V·∂ᵢu₀ = -F_tildeᵢ`,
   `V·∂ᵢ∂ⱼu₀ = ½(U_tildeᵢⱼ - hᵢⱼ)`; the transported Günther identity gives
   `∂ᵢV·∂ⱼV = ∂ᵢF_tildeⱼ + ∂ⱼF_tildeᵢ + U_tildeᵢⱼ`; the product rule finishes.

## Main statements

* `gunther_perturbation` — Günther's perturbation theorem (Wassermann's Theorem B).
-/

open scoped BigOperators ContDiff
open Filter Topology NashEmbedding.Sobolev Matrix

noncomputable
section

namespace NashEmbedding

variable {n N : ℕ}

/-! ## Free maps and their dual frame -/

/-- Index set of the frame: first derivatives, and second derivatives `∂ₚ∂_q` with `p ≤ q`. -/
abbrev FrameIdx (n : ℕ) := Fin n ⊕ {pq : Fin n × Fin n // pq.1 ≤ pq.2}

/-- The frame `{∂ᵢu} ∪ {∂ₚ∂_q u}_{p ≤ q}` of a map `u`. -/
def frame (u : (Fin n → ℝ) → (Fin N → ℝ)) : FrameIdx n → (Fin n → ℝ) → (Fin N → ℝ)
  | Sum.inl i => pderiv i u
  | Sum.inr pq => pderiv pq.1.1 (pderiv pq.1.2 u)

/-- A map is *free* if its frame is linearly independent at every point. -/
def IsFree (u : (Fin n → ℝ) → (Fin N → ℝ)) : Prop := IsPointwiseLinIndep (frame u)

lemma frame_smoothPeriodic {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u) :
    ∀ k, SmoothPeriodic (frame u k)
  | Sum.inl i => hu.pderiv i
  | Sum.inr pq => (hu.pderiv pq.1.2).pderiv pq.1.1

/-- The second-derivative part of the dual frame, extended by `0` to pairs `p > q`. -/
def dualB (u : (Fin n → ℝ) → (Fin N → ℝ)) (p q : Fin n) : (Fin n → ℝ) → (Fin N → ℝ) :=
  if hpq : p ≤ q then dualFrame (frame u) (Sum.inr ⟨(p, q), hpq⟩) else 0

/-- The first-derivative part of the dual frame. -/
def dualA (u : (Fin n → ℝ) → (Fin N → ℝ)) (i : Fin n) : (Fin n → ℝ) → (Fin N → ℝ) :=
  dualFrame (frame u) (Sum.inl i)

/-! ## The base level and the size of a perturbation -/

/-- Base Sobolev level `r = ⌊n/2⌋ + 4`, so that `n/2 + 3 < r`. -/
def bLevel (n : ℕ) : ℕ := n / 2 + 4

lemma bLevel_gt (n : ℕ) : 1 + (n : ℝ) / 2 < (bLevel n : ℝ) - 2 := by
  unfold bLevel
  have h : ((n / 2 : ℕ) : ℝ) ≥ (n : ℝ) / 2 - 1 / 2 := by
    have := Nat.div_add_mod n 2
    have hmod : (n % 2 : ℕ) ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num))
    have h1 : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) = n := by exact_mod_cast this
    have h2 : ((n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hmod
    linarith
  push_cast
  linarith

-- `bLevel n = n / 2 + 4` must not be unfolded by `whnf` (symbolic `Nat.div` is expensive).
attribute [irreducible] bLevel

/-- The `H^r` size of a matrix-valued perturbation: the sum over entries of the squared
`H^r` norms of the coefficient sequences. -/
def hSize (n : ℕ) (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x i j : ℝ) : ℂ)))

/-! ## The momentum-side data -/

/-- The Günther data of `u₀` and `h`: coefficients of the dual frame and of `h`. -/
def bData (n : ℕ) (u₀ : (Fin n → ℝ) → (Fin N → ℝ))
    (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : GuntherData n N where
  a i := vcoeff n (dualA u₀ i)
  b p q := vcoeff n (dualB u₀ p q)
  h p q := stdFourierCoeff n (fun x => ((h x p q : ℝ) : ℂ))

/-- Realness of the data: all sequences are `conjReflect`-fixed. -/
structure GuntherData.Real (d : GuntherData n N) : Prop where
  a_real : ∀ i, VReal (d.a i)
  b_real : ∀ p q, VReal (d.b p q)
  h_real : ∀ p q, conjReflect (d.h p q) = d.h p q

lemma dualA_smoothPeriodic {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u)
    (hfree : IsFree u) (i : Fin n) : SmoothPeriodic (dualA u i) :=
  dualFrame_smoothPeriodic hfree (frame_smoothPeriodic hu) _

lemma dualB_smoothPeriodic {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u)
    (hfree : IsFree u) (p q : Fin n) : SmoothPeriodic (dualB u p q) := by
  unfold dualB
  split_ifs with hpq
  · exact dualFrame_smoothPeriodic hfree (frame_smoothPeriodic hu) _
  · exact ⟨contDiff_const, fun _ _ => rfl⟩

lemma bData_smooth (hn : 0 < n) {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u₀)
    (hfree : IsFree u₀) {h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hh : SmoothPeriodic h) :
    (bData n u₀ h).Smooth where
  a_mem i k := (vcoeff_vrapid hn (dualA_smoothPeriodic hu hfree i)).vmem k
  b_mem p q k := (vcoeff_vrapid hn (dualB_smoothPeriodic hu hfree p q)).vmem k
  h_mem p q k := by
    have hs : ContDiff ℝ ∞ (fun x => ((h x p q : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_pi.mp (contDiff_pi.mp hh.smooth p) q)
    have hp : IsPeriodic2Pi (fun x => ((h x p q : ℝ) : ℂ)) := fun x k => by
      simp [hh.periodic x k]
    exact isRapidDecay_stdFourierCoeff hn hs hp k

lemma bData_real {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} {h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
  (hh : SmoothPeriodic h) :
    (bData n u₀ h).Real where
  a_real i := vcoeff_vreal
  b_real p q := vcoeff_vreal
  h_real p q := by
    have hc : Continuous (fun x => ((h x p q : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply q).comp ((continuous_apply p).comp hh.smooth.continuous))
    exact conjReflect_stdFourierCoeff_of_real (fun x => by simp)

/-! ## Smallness: the constant term -/

/-- Multiplication by a scalar sequence, at level `s` with `2s > n` (MT2 componentwise). -/
lemma vecNormSq_smulSeq_le (hn : 0 < n) {s : ℝ} (hs : (n : ℝ) < 2 * s) {f : Seq n}
    (hf : MemSobolev n s f) {a : VecSeq n N} (ha : VMem n N s a) :
    vecNormSq n N s (smulSeq f a) ≤ mt2Const n s * sobolevNormSq n s f * vecNormSq n N s a := by
  unfold vecNormSq smulSeq
  calc ∑ α, sobolevNormSq n s (seqConv f (a α))
      ≤ ∑ α, mt2Const n s * sobolevNormSq n s f * sobolevNormSq n s (a α) :=
        Finset.sum_le_sum fun α _ => (second_multiplication_theorem_seq hn hs hf (ha α)).2
    _ = mt2Const n s * sobolevNormSq n s f * ∑ α, sobolevNormSq n s (a α) := by
        rw [Finset.mul_sum]

lemma vmem_smulSeq (hn : 0 < n) {s : ℝ} (hs : (n : ℝ) < 2 * s) {f : Seq n}
    (hf : MemSobolev n s f) {a : VecSeq n N} (ha : VMem n N s a) : VMem n N s (smulSeq f a) :=
  fun α => (second_multiplication_theorem_seq hn hs hf (ha α)).1

lemma mt2Const_nonneg (n : ℕ) (s : ℝ) : 0 ≤ mt2Const n s := by
  unfold mt2Const sobolevEmbedConstSq
  exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (tsum_nonneg fun _ =>
      weight_nonneg _ _)

/-- The constant controlling `‖c‖²_(r)` in terms of `hSize`: depends on `u₀` only. -/
def cConst (n N : ℕ) (u₀ : (Fin n → ℝ) → (Fin N → ℝ)) : ℝ :=
  (pairs n).card * (mt2Const n (bLevel n) / 4)
    * ∑ pq ∈ pairs n, vecNormSq n N (bLevel n) (vcoeff n (dualB u₀ pq.1 pq.2))

lemma cConst_nonneg (u₀ : (Fin n → ℝ) → (Fin N → ℝ)) : 0 ≤ cConst n N u₀ := by
  unfold cConst
  have h1 : 0 ≤ mt2Const n (bLevel n) := mt2Const_nonneg n _
  have h2 : 0 ≤ ∑ pq ∈ pairs n, vecNormSq n N (bLevel n) (vcoeff n (dualB u₀ pq.1 pq.2)) :=
    Finset.sum_nonneg fun _ _ => vecNormSq_nonneg _ _
  positivity

/-- `‖c‖²_(r) ≤ cConst · hSize h`. -/
lemma gC_bound (hn : 0 < n) {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u₀)
    (hfree : IsFree u₀) {h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hh : SmoothPeriodic h) :
    vecNormSq n N (bLevel n) (gC (bData n u₀ h)) ≤ cConst n N u₀ * hSize n h := by
  have hr : (n : ℝ) < 2 * ((bLevel n : ℕ) : ℝ) := by have := bLevel_gt n; linarith
  have hds := bData_smooth hn hu hfree hh
  have hK := mt2Const_nonneg n (bLevel n)
  -- each summand
  have hterm : ∀ pq ∈ pairs n,
      vecNormSq n N (bLevel n) (smulSeq (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m)
        ((bData n u₀ h).b pq.1 pq.2))
      ≤ (mt2Const n (bLevel n) / 4) * hSize n h * vecNormSq n N (bLevel n) ((bData n u₀ h).b
          pq.1 pq.2) := by
    intro pq _
    have hf : MemSobolev n (bLevel n) (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m) :=
      (hds.h_mem pq.1 pq.2 (bLevel n)).smul _
    have h1 := vecNormSq_smulSeq_le hn hr hf (hds.b_mem pq.1 pq.2 (bLevel n))
    rw [sobolevNormSq_smul] at h1
    have hh2 : (bData n u₀ h).h pq.1 pq.2 = stdFourierCoeff n (fun x => ((h x pq.1 pq.2 : ℝ) :
        ℂ)) := rfl
    rw [hh2] at h1
    have h2 : sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x pq.1 pq.2 : ℝ) :
        ℂ))) ≤ hSize n h := by
      unfold hSize
      obtain ⟨p, q⟩ := pq
      calc sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x p q : ℝ) : ℂ)))
          ≤ ∑ j, sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x p j : ℝ) : ℂ))) :=
            Finset.single_le_sum
              (f := fun j => sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x p j :
                  ℝ) : ℂ))))
              (fun j _ => sobolevNormSq_nonneg _ _) (Finset.mem_univ q)
        _ ≤ ∑ i, ∑ j, sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x i j : ℝ) :
            ℂ))) :=
            Finset.single_le_sum
              (f := fun i => ∑ j, sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x
                  i j : ℝ) : ℂ))))
              (fun i _ => Finset.sum_nonneg fun j _ => sobolevNormSq_nonneg _ _) (Finset.mem_univ p)
    have hnorm : ‖(1 / 2 : ℂ)‖ ^ 2 = 1 / 4 := by norm_num
    rw [hnorm] at h1
    have hb0 := vecNormSq_nonneg ((bLevel n : ℕ) : ℝ) ((bData n u₀ h).b pq.1 pq.2)
    have h3 : mt2Const n (bLevel n) * (1 / 4 * sobolevNormSq n (bLevel n)
          (stdFourierCoeff n (fun x => ((h x pq.1 pq.2 : ℝ) : ℂ))))
        ≤ mt2Const n (bLevel n) / 4 * hSize n h := by nlinarith
    exact le_trans h1 (mul_le_mul_of_nonneg_right h3 hb0)
  have hmem : ∀ pq ∈ pairs n, VMem n N (bLevel n)
      (smulSeq (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m) ((bData n u₀ h).b pq.1
          pq.2)) :=
    fun pq _ => vmem_smulSeq hn hr ((hds.h_mem pq.1 pq.2 (bLevel n)).smul _) (hds.b_mem pq.1
        pq.2 (bLevel n))
  unfold gC
  rw [vecNormSq_neg]
  calc vecNormSq n N (bLevel n) (∑ pq ∈ pairs n, smulSeq (fun m => (1 / 2 : ℂ) * (bData n u₀
      h).h pq.1 pq.2 m)
          ((bData n u₀ h).b pq.1 pq.2))
      ≤ (pairs n).card * ∑ pq ∈ pairs n, vecNormSq n N (bLevel n)
          (smulSeq (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m) ((bData n u₀ h).b pq.1
              pq.2)) :=
        vecNormSq_finset_sum_le _ hmem
    _ ≤ (pairs n).card * ∑ pq ∈ pairs n,
          (mt2Const n (bLevel n) / 4) * hSize n h * vecNormSq n N (bLevel n) ((bData n u₀ h).b
              pq.1 pq.2) := by
        gcongr with pq hpq
        exact hterm pq hpq
    _ = cConst n N u₀ * hSize n h := by
        unfold cConst
        simp only [bData]
        rw [← Finset.mul_sum]
        ring

lemma hSize_nonneg (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : 0 ≤ hSize n h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sobolevNormSq_nonneg _ _

/-! ## Closure of rapid decay and of realness under the Günther operations -/

private lemma vrapid_vpartial {v : VecSeq n N} (hv : VRapid n N v) (i : Fin n) :
    VRapid n N (vpartial i v) := fun α => (hv α).partialCoeff i

private lemma vrapid_vlap {v : VecSeq n N} (hv : VRapid n N v) : VRapid n N (vlap v) :=
  fun α => ((hv α).laplacianCoeff).neg

private lemma isRapidDecay_dotConv (hn : 0 < n) {v w : VecSeq n N} (hv : VRapid n N v)
    (hw : VRapid n N w) : IsRapidDecay n (dotConv v w) :=
  IsRapidDecay.finset_sum Finset.univ (fun α _ => IsRapidDecay.seqConv hn (hv α) (hw α))

private lemma isRapidDecay_Fb (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (i : Fin n) :
    IsRapidDecay n (Fb i v v) :=
  (isRapidDecay_dotConv hn (vrapid_vlap hv) (vrapid_vpartial hv i)).resolventCoeff.neg

private lemma isRapidDecay_Ub (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (i j : Fin n) :
    IsRapidDecay n (Ub i j v v) := by
  have h1 : IsRapidDecay n (resolventCoeff (dotConv (vpartial i v) (vpartial j v))) :=
    (isRapidDecay_dotConv hn (vrapid_vpartial hv i) (vrapid_vpartial hv j)).resolventCoeff
  have h2 : IsRapidDecay n (fun m => (2 : ℂ) *
      resolventCoeff (dotConv (vlap v) (vpartial i (vpartial j v))) m) :=
    ((isRapidDecay_dotConv hn (vrapid_vlap hv)
      (vrapid_vpartial (vrapid_vpartial hv j) i)).resolventCoeff).const_mul 2
  have h3 : IsRapidDecay n (fun m => (2 : ℂ) * ∑ k, resolventCoeff
      (dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))) m) :=
    (IsRapidDecay.finset_sum Finset.univ (fun k _ =>
      (isRapidDecay_dotConv hn (vrapid_vpartial (vrapid_vpartial hv k) i)
        (vrapid_vpartial (vrapid_vpartial hv k) j)).resolventCoeff)).const_mul 2
  exact (h1.add h2).sub h3

private lemma conjReflect_neg' (a : Seq n) :
    conjReflect (fun m => -a m) = fun m => -conjReflect a m := by
  funext m; simp [conjReflect]

private lemma conjReflect_const_mul_of_real {c : ℂ} (hc : (starRingEnd ℂ) c = c) {a : Seq n}
    (ha : conjReflect a = a) : conjReflect (fun m => c * a m) = fun m => c * a m := by
  funext m
  have h := congrFun ha m
  simp only [conjReflect, map_mul] at *
  rw [hc, h]

private lemma conjReflect_seqConv_of_fixed {a b : Seq n} (ha : conjReflect a = a)
    (hb : conjReflect b = b) : conjReflect (seqConv a b) = seqConv a b := by
  rw [conjReflect_seqConv, ha, hb]

private lemma vreal_vpartial {v : VecSeq n N} (hv : VReal v) (i : Fin n) :
    VReal (vpartial i v) := fun α => by
  change conjReflect (partialCoeff i (v α)) = partialCoeff i (v α)
  rw [conjReflect_partialCoeff, hv α]

private lemma vreal_vlap {v : VecSeq n N} (hv : VReal v) : VReal (vlap v) := fun α => by
  change conjReflect (fun m => -(laplacianCoeff (v α) m)) = _
  rw [conjReflect_neg', conjReflect_laplacianCoeff, hv α]
  rfl

private lemma conjReflect_dotConv {v w : VecSeq n N} (hv : VReal v) (hw : VReal w) :
    conjReflect (dotConv v w) = dotConv v w := by
  change conjReflect (fun m => ∑ α, seqConv (v α) (w α) m) = _
  rw [conjReflect_finset_sum]
  funext m
  change ∑ α, conjReflect (seqConv (v α) (w α)) m = ∑ α, seqConv (v α) (w α) m
  exact Finset.sum_congr rfl fun α _ =>
    congrFun (conjReflect_seqConv_of_fixed (hv α) (hw α)) m

private lemma conjReflect_resolvent_dotConv {v w : VecSeq n N} (hv : VReal v) (hw : VReal w) :
    conjReflect (resolventCoeff (dotConv v w)) = resolventCoeff (dotConv v w) := by
  rw [conjReflect_resolventCoeff, conjReflect_dotConv hv hw]

private lemma conjReflect_Fb {v : VecSeq n N} (hv : VReal v) (i : Fin n) :
    conjReflect (Fb i v v) = Fb i v v := by
  change conjReflect (fun m => -(resolventCoeff (dotConv (vlap v) (vpartial i v)) m)) = _
  rw [conjReflect_neg', conjReflect_resolvent_dotConv (vreal_vlap hv) (vreal_vpartial hv i)]
  rfl

private lemma conjReflect_Ub {v : VecSeq n N} (hv : VReal v) (i j : Fin n) :
    conjReflect (Ub i j v v) = Ub i j v v := by
  have hc2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  have h1 := conjReflect_resolvent_dotConv (vreal_vpartial hv i) (vreal_vpartial hv j)
  have h2 := conjReflect_const_mul_of_real hc2
    (conjReflect_resolvent_dotConv (vreal_vlap hv) (vreal_vpartial (vreal_vpartial hv j) i))
  have h3 : conjReflect (fun m => ∑ k, resolventCoeff
      (dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))) m)
      = fun m => ∑ k, resolventCoeff
      (dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))) m := by
    rw [conjReflect_finset_sum]
    funext m
    exact Finset.sum_congr rfl fun k _ => congrFun
      (conjReflect_resolvent_dotConv (vreal_vpartial (vreal_vpartial hv k) i)
        (vreal_vpartial (vreal_vpartial hv k) j)) m
  have h4 := conjReflect_const_mul_of_real hc2 h3
  change conjReflect (fun m => (resolventCoeff (dotConv (vpartial i v) (vpartial j v)) m
      + (2 : ℂ) * resolventCoeff (dotConv (vlap v) (vpartial i (vpartial j v))) m)
      - (2 : ℂ) * ∑ k, resolventCoeff
          (dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))) m) = _
  rw [conjReflect_sub, conjReflect_add, h1, h2, h4]
  rfl

/-! ## Realness is preserved by the iteration -/

lemma vreal_zero : VReal (0 : VecSeq n N) := fun _ => by funext m; simp [conjReflect]

lemma vreal_gT {d : GuntherData n N} (hd : d.Real) {v : VecSeq n N} (hv : VReal v) :
    VReal (gC d + gB d v v) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  intro α
  have hform : (gC d + gB d v v) α = fun m =>
      -(∑ pq ∈ pairs n, seqConv (fun m => (1 / 2 : ℂ) * d.h pq.1 pq.2 m) (d.b pq.1 pq.2 α) m)
      + (-(∑ i, seqConv (Fb i v v) (d.a i α) m)
         + ∑ pq ∈ pairs n,
            seqConv (fun m => (1 / 2 : ℂ) * Ub pq.1 pq.2 v v m) (d.b pq.1 pq.2 α) m) := by
    funext m
    simp [gC, gB, smulSeq, Finset.sum_apply]
  have hs1 : conjReflect (fun m =>
      ∑ pq ∈ pairs n, seqConv (fun m => (1 / 2 : ℂ) * d.h pq.1 pq.2 m) (d.b pq.1 pq.2 α) m)
      = fun m => ∑ pq ∈ pairs n,
        seqConv (fun m => (1 / 2 : ℂ) * d.h pq.1 pq.2 m) (d.b pq.1 pq.2 α) m := by
    rw [conjReflect_finset_sum]
    funext m
    exact Finset.sum_congr rfl fun pq _ => congrFun (conjReflect_seqConv_of_fixed
      (conjReflect_const_mul_of_real hhalf (hd.h_real pq.1 pq.2)) (hd.b_real pq.1 pq.2 α)) m
  have hs2 : conjReflect (fun m => ∑ i, seqConv (Fb i v v) (d.a i α) m)
      = fun m => ∑ i, seqConv (Fb i v v) (d.a i α) m := by
    rw [conjReflect_finset_sum]
    funext m
    exact Finset.sum_congr rfl fun i _ => congrFun
      (conjReflect_seqConv_of_fixed (conjReflect_Fb hv i) (hd.a_real i α)) m
  have hs3 : conjReflect (fun m =>
      ∑ pq ∈ pairs n, seqConv (fun m => (1 / 2 : ℂ) * Ub pq.1 pq.2 v v m) (d.b pq.1 pq.2 α) m)
      = fun m => ∑ pq ∈ pairs n,
        seqConv (fun m => (1 / 2 : ℂ) * Ub pq.1 pq.2 v v m) (d.b pq.1 pq.2 α) m := by
    rw [conjReflect_finset_sum]
    funext m
    exact Finset.sum_congr rfl fun pq _ => congrFun (conjReflect_seqConv_of_fixed
      (conjReflect_const_mul_of_real hhalf (conjReflect_Ub hv pq.1 pq.2))
      (hd.b_real pq.1 pq.2 α)) m
  rw [hform, conjReflect_add, conjReflect_neg', hs1, conjReflect_add, conjReflect_neg', hs2, hs3]

lemma vreal_of_tendsto {u : ℕ → VecSeq n N} {a : VecSeq n N} (hu : ∀ p, VReal (u p))
    (hlim : ∀ α m, Tendsto (fun p => u p α m) atTop (𝓝 (a α m))) : VReal a := by
  intro α
  funext m
  -- `conjReflect (u p α) m = u p α m` for all `p`; pass to the limit
  have h1 : Tendsto (fun p => conjReflect (u p α) m) atTop (𝓝 (conjReflect (a α) m)) := by
    unfold conjReflect
    exact (Complex.continuous_conj.tendsto _).comp (hlim α (-m))
  have h2 : (fun p => conjReflect (u p α) m) = fun p => u p α m := by
    funext p; rw [hu p α]
  rw [h2] at h1
  exact tendsto_nhds_unique h1 (hlim α m)

/-! ## Position-space pieces of the fixed point -/

/-- Real synthesis of a scalar sequence. -/
def ssynth (n : ℕ) (f : Seq n) : (Fin n → ℝ) → ℝ := fun x => (fourierSynthesis n f x).re

private lemma ssynth_smoothPeriodic (hn : 0 < n) {f : Seq n} (hf : IsRapidDecay n f) :
    SmoothPeriodic (ssynth n f) := by
  constructor
  · have h := Complex.reCLM.contDiff.comp (fourierSynthesis_contDiff hn hf)
    unfold ssynth
    exact h
  · intro x k
    unfold ssynth
    rw [fourierSynthesis_isPeriodic2Pi x k]

/-- For a rapidly decaying, `conjReflect`-fixed sequence, the coefficients of the real
synthesis are the sequence itself. -/
private lemma stdFourierCoeff_ssynth (hn : 0 < n) {f : Seq n} (hf : IsRapidDecay n f)
    (hfix : conjReflect f = f) :
    stdFourierCoeff n (fun x => ((ssynth n f x : ℝ) : ℂ)) = f := by
  have h : (fun x => ((ssynth n f x : ℝ) : ℂ)) = fourierSynthesis n f := by
    funext x
    exact Complex.ext (by simp [ssynth]) (by simp [ssynth, fourierSynthesis_im_eq_zero hfix x])
  rw [h]
  funext m
  exact stdFourierCoeff_fourierSynthesis_of_rapidDecay hn hf m

private lemma continuous_ofReal_of_contDiff {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun y => ((f y : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hf.continuous

private lemma isPeriodic2Pi_const_mul {f : (Fin n → ℝ) → ℂ} (hf : IsPeriodic2Pi f) (c : ℂ) :
    IsPeriodic2Pi (fun x => c * f x) := fun x k => by
  change c * f (x + periodicShift n k) = c * f x
  rw [hf x k]

/-- The position-space `F_tildeᵢ`. -/
def Ftil (n : ℕ) (v : VecSeq n N) (i : Fin n) : (Fin n → ℝ) → ℝ := ssynth n (Fb i v v)

/-- The position-space `U_tildeᵢⱼ`. -/
def Util (n : ℕ) (v : VecSeq n N) (i j : Fin n) : (Fin n → ℝ) → ℝ := ssynth n (Ub i j v v)

/-- The position-space right-hand side `W = -∑ᵢ F_tildeᵢ Dᵢ + ∑_{p≤q} ½(U_tilde_{pq} - h_{pq})
D_{pq}`. -/
def Wfun (n : ℕ) (u₀ : (Fin n → ℝ) → (Fin N → ℝ)) (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (v : VecSeq n N) : (Fin n → ℝ) → (Fin N → ℝ) :=
  fun x => -(∑ i, Ftil n v i x • dualA u₀ i x)
    + ∑ pq ∈ pairs n, ((1 / 2 : ℝ) * (Util n v pq.1 pq.2 x - h x pq.1 pq.2)) • dualB u₀ pq.1 pq.2 x

lemma Ftil_smoothPeriodic (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v)
    (i : Fin n) : SmoothPeriodic (Ftil n v i) :=
  ssynth_smoothPeriodic hn (isRapidDecay_Fb hn hv i)

lemma Util_smoothPeriodic (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v)
    (i j : Fin n) : SmoothPeriodic (Util n v i j) :=
  ssynth_smoothPeriodic hn (isRapidDecay_Ub hn hv i j)

/-- The coefficients of `F_tildeᵢ` are `Fb i v v`. -/
private lemma coeff_Ftil (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v)
    (i : Fin n) : stdFourierCoeff n (fun x => ((Ftil n v i x : ℝ) : ℂ)) = Fb i v v :=
  stdFourierCoeff_ssynth hn (isRapidDecay_Fb hn hv i) (conjReflect_Fb hr i)

/-- The coefficients of `U_tildeᵢⱼ` are `Ub i j v v`. -/
private lemma coeff_Util (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v)
    (i j : Fin n) : stdFourierCoeff n (fun x => ((Util n v i j x : ℝ) : ℂ)) = Ub i j v v :=
  stdFourierCoeff_ssynth hn (isRapidDecay_Ub hn hv i j) (conjReflect_Ub hr i j)

lemma Util_symm {v : VecSeq n N} (i j : Fin n) :
    Util n v i j = Util n v j i := by
  unfold Util; rw [Ub_symm i j]

/-- **Coefficients of `W` are `T v`.** -/
theorem vcoeff_Wfun (hn : 0 < n) {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u₀)
    (hfree : IsFree u₀) {h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hh : SmoothPeriodic h)
    {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v) :
    vcoeff n (Wfun n u₀ h v) = gC (bData n u₀ h) + gB (bData n u₀ h) v v := by
  have hF : ∀ i, SmoothPeriodic (Ftil n v i) := fun i => Ftil_smoothPeriodic hn hv i
  have hU : ∀ p q, SmoothPeriodic (Util n v p q) := fun p q => Util_smoothPeriodic hn hv p q
  have hA : ∀ i, SmoothPeriodic (dualA u₀ i) := fun i => dualA_smoothPeriodic hu hfree i
  have hB : ∀ p q, SmoothPeriodic (dualB u₀ p q) := fun p q => dualB_smoothPeriodic hu hfree p q
  have hhs : ∀ p q : Fin n, SmoothPeriodic (fun x => h x p q) := fun p q =>
    ⟨contDiff_pi.mp (contDiff_pi.mp hh.smooth p) q, fun x k => by rw [hh.periodic x k]⟩
  funext α
  -- the complexified position-space factors
  have cFt : ∀ i, ContDiff ℝ ∞ (fun x => ((Ftil n v i x : ℝ) : ℂ))
      ∧ IsPeriodic2Pi (fun x => ((Ftil n v i x : ℝ) : ℂ)) :=
    fun i => smoothPeriodic_ofReal_scalar (hF i)
  have cUt : ∀ p q, ContDiff ℝ ∞ (fun x => ((Util n v p q x : ℝ) : ℂ))
      ∧ IsPeriodic2Pi (fun x => ((Util n v p q x : ℝ) : ℂ)) :=
    fun p q => smoothPeriodic_ofReal_scalar (hU p q)
  have cAv : ∀ i, ContDiff ℝ ∞ (fun x => ((dualA u₀ i x α : ℝ) : ℂ))
      ∧ IsPeriodic2Pi (fun x => ((dualA u₀ i x α : ℝ) : ℂ)) :=
    fun i => smoothPeriodic_ofReal_comp (hA i) α
  have cBv : ∀ p q, ContDiff ℝ ∞ (fun x => ((dualB u₀ p q x α : ℝ) : ℂ))
      ∧ IsPeriodic2Pi (fun x => ((dualB u₀ p q x α : ℝ) : ℂ)) :=
    fun p q => smoothPeriodic_ofReal_comp (hB p q) α
  have cHv : ∀ p q : Fin n, ContDiff ℝ ∞ (fun x => ((h x p q : ℝ) : ℂ))
      ∧ IsPeriodic2Pi (fun x => ((h x p q : ℝ) : ℂ)) :=
    fun p q => smoothPeriodic_ofReal_scalar (hhs p q)
  -- coefficients of each product
  have cA : ∀ i, stdFourierCoeff n
      (fun x => ((Ftil n v i x : ℝ) : ℂ) * ((dualA u₀ i x α : ℝ) : ℂ))
      = seqConv (Fb i v v) ((bData n u₀ h).a i α) := by
    intro i
    rw [stdFourierCoeff_mul hn (cFt i).1 (cFt i).2 (cAv i).1 (cAv i).2, coeff_Ftil hn hv hr i]
    rfl
  have cU2 : ∀ pq : Fin n × Fin n, stdFourierCoeff n
      (fun x => ((1 / 2 : ℂ) * ((Util n v pq.1 pq.2 x : ℝ) : ℂ))
        * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ))
      = seqConv (fun m => (1 / 2 : ℂ) * Ub pq.1 pq.2 v v m) ((bData n u₀ h).b pq.1 pq.2 α) := by
    intro pq
    rw [stdFourierCoeff_mul hn (contDiff_const.mul (cUt pq.1 pq.2).1)
        (isPeriodic2Pi_const_mul (cUt pq.1 pq.2).2 _) (cBv pq.1 pq.2).1 (cBv pq.1 pq.2).2,
      stdFourierCoeff_const_mul, coeff_Util hn hv hr pq.1 pq.2]
    rfl
  have cH2 : ∀ pq : Fin n × Fin n, stdFourierCoeff n
      (fun x => ((1 / 2 : ℂ) * ((h x pq.1 pq.2 : ℝ) : ℂ)) * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ))
      = seqConv (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m)
          ((bData n u₀ h).b pq.1 pq.2 α) := by
    intro pq
    rw [stdFourierCoeff_mul hn (contDiff_const.mul (cHv pq.1 pq.2).1)
        (isPeriodic2Pi_const_mul (cHv pq.1 pq.2).2 _) (cBv pq.1 pq.2).1 (cBv pq.1 pq.2).2,
      stdFourierCoeff_const_mul]
    rfl
  -- the position-space expansion of `W`
  have hfun : (fun x => ((Wfun n u₀ h v x α : ℝ) : ℂ))
      = fun x => -(∑ i, ((Ftil n v i x : ℝ) : ℂ) * ((dualA u₀ i x α : ℝ) : ℂ))
        + ∑ pq ∈ pairs n, (((1 / 2 : ℂ) * ((Util n v pq.1 pq.2 x : ℝ) : ℂ))
              * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ)
            - ((1 / 2 : ℂ) * ((h x pq.1 pq.2 : ℝ) : ℂ)) * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ)) := by
    funext x
    simp only [Wfun, Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun pq _ => by ring
  -- continuity of the pieces
  have ctA : ∀ i, Continuous (fun x => ((Ftil n v i x : ℝ) : ℂ) * ((dualA u₀ i x α : ℝ) : ℂ)) :=
    fun i => ((cFt i).1.continuous).mul ((cAv i).1.continuous)
  have ctU : ∀ pq : Fin n × Fin n, Continuous (fun x =>
      ((1 / 2 : ℂ) * ((Util n v pq.1 pq.2 x : ℝ) : ℂ)) * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ)) :=
    fun pq => (continuous_const.mul (cUt pq.1 pq.2).1.continuous).mul (cBv pq.1 pq.2).1.continuous
  have ctH : ∀ pq : Fin n × Fin n, Continuous (fun x =>
      ((1 / 2 : ℂ) * ((h x pq.1 pq.2 : ℝ) : ℂ)) * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ)) :=
    fun pq => (continuous_const.mul (cHv pq.1 pq.2).1.continuous).mul (cBv pq.1 pq.2).1.continuous
  have ctN : Continuous
      (fun x => -∑ i, ((Ftil n v i x : ℝ) : ℂ) * ((dualA u₀ i x α : ℝ) : ℂ)) :=
    (continuous_finsetSum _ fun i _ => ctA i).neg
  have ctS2 : Continuous (fun x => ∑ pq ∈ pairs n,
      (((1 / 2 : ℂ) * ((Util n v pq.1 pq.2 x : ℝ) : ℂ)) * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ)
        - ((1 / 2 : ℂ) * ((h x pq.1 pq.2 : ℝ) : ℂ)) * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ))) :=
    continuous_finsetSum _ fun pq _ => (ctU pq).sub (ctH pq)
  change stdFourierCoeff n (fun x => ((Wfun n u₀ h v x α : ℝ) : ℂ)) = _
  rw [hfun, stdFourierCoeff_add ctN ctS2, stdFourierCoeff_neg,
    stdFourierCoeff_finset_sum' _ (fun i _ => ctA i),
    stdFourierCoeff_finset_sum' (f := fun pq x =>
      ((1 / 2 : ℂ) * ((Util n v pq.1 pq.2 x : ℝ) : ℂ)) *
          ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ) -
        ((1 / 2 : ℂ) * ((h x pq.1 pq.2 : ℝ) : ℂ)) *
          ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ)) (pairs n)
      (fun pq _ => by exact (ctU pq).sub (ctH pq))]
  funext m
  simp only [gC, gB, smulSeq, Pi.add_apply, Pi.neg_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => congrFun (cA i) m)]
  rw [Finset.sum_congr rfl (fun pq (_ : pq ∈ pairs n) => by
    rw [stdFourierCoeff_sub (ctU pq) (ctH pq)]
    change stdFourierCoeff n _ m - stdFourierCoeff n _ m = _
    rw [cU2 pq, cH2 pq] :
    ∀ pq ∈ pairs n, stdFourierCoeff n (fun x =>
      ((1 / 2 : ℂ) * ((Util n v pq.1 pq.2 x : ℝ) : ℂ)) * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ)
        - ((1 / 2 : ℂ) * ((h x pq.1 pq.2 : ℝ) : ℂ)) * ((dualB u₀ pq.1 pq.2 x α : ℝ) : ℂ)) m
      = seqConv (fun m => (1 / 2 : ℂ) * Ub pq.1 pq.2 v v m) ((bData n u₀ h).b pq.1 pq.2 α) m
        - seqConv (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m)
            ((bData n u₀ h).b pq.1 pq.2 α) m)]
  rw [Finset.sum_sub_distrib]
  ring

lemma Wfun_smoothPeriodic (hn : 0 < n) {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u₀)
    (hfree : IsFree u₀) {h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hh : SmoothPeriodic h)
    {v : VecSeq n N} (hv : VRapid n N v) :
    SmoothPeriodic (Wfun n u₀ h v) := by
  have hF : ∀ i, SmoothPeriodic (Ftil n v i) := fun i => Ftil_smoothPeriodic hn hv i
  have hU : ∀ p q, SmoothPeriodic (Util n v p q) := fun p q => Util_smoothPeriodic hn hv p q
  have hA : ∀ i, SmoothPeriodic (dualA u₀ i) := fun i => dualA_smoothPeriodic hu hfree i
  have hB : ∀ p q, SmoothPeriodic (dualB u₀ p q) := fun p q => dualB_smoothPeriodic hu hfree p q
  have hhc : ∀ p q : Fin n, ContDiff ℝ ∞ (fun x => h x p q) := fun p q =>
    contDiff_pi.mp (contDiff_pi.mp hh.smooth p) q
  constructor
  · unfold Wfun
    refine ContDiff.add (ContDiff.neg (ContDiff.sum fun i _ => ?_)) (ContDiff.sum fun pq _ => ?_)
    · exact ContDiff.smul (f := fun x => Ftil n v i x) (g := fun x => dualA u₀ i x)
        (hF i).smooth (hA i).smooth
    · exact ContDiff.smul (f := fun x => (1 / 2 : ℝ) * (Util n v pq.1 pq.2 x - h x pq.1 pq.2))
        (g := fun x => dualB u₀ pq.1 pq.2 x)
        (contDiff_const.mul ((hU pq.1 pq.2).smooth.sub (hhc pq.1 pq.2))) (hB pq.1 pq.2).smooth
  · intro x k
    unfold Wfun
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [(hF i).periodic x k, (hA i).periodic x k]
    · exact Finset.sum_congr rfl fun pq _ => by
        rw [(hU pq.1 pq.2).periodic x k, (hB pq.1 pq.2).periodic x k, hh.periodic x k]

/-- **The product identity in position space**: for `V = vsynth v`,
`∂ᵢV · ∂ⱼV = ∂ᵢF_tildeⱼ + ∂ⱼF_tildeᵢ + U_tildeᵢⱼ`. -/
theorem pderiv_dot_pderiv_vsynth (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v)
    (hr : VReal v) (i j : Fin n) (x : Fin n → ℝ) :
    pderiv i (vsynth n v) x ⬝ᵥ pderiv j (vsynth n v) x
      = pderiv i (Ftil n v j) x + pderiv j (Ftil n v i) x + Util n v i j x := by
  have hFi := Ftil_smoothPeriodic hn hv i
  have hFj := Ftil_smoothPeriodic hn hv j
  have hUij := Util_smoothPeriodic hn hv i j
  have hVsp : SmoothPeriodic (vsynth n v) := vsynth_smoothPeriodic hn hv
  have hL : SmoothPeriodic (fun y => pderiv i (vsynth n v) y ⬝ᵥ pderiv j (vsynth n v) y) :=
    (hVsp.pderiv i).dotProduct (hVsp.pderiv j)
  have hR : SmoothPeriodic
      (fun y => pderiv i (Ftil n v j) y + pderiv j (Ftil n v i) y + Util n v i j y) := by
    constructor
    · exact ((pderiv_contDiff hFj.smooth i).add (pderiv_contDiff hFi.smooth j)).add hUij.smooth
    · intro y k
      change pderiv i (Ftil n v j) (y + periodicShift n k)
          + pderiv j (Ftil n v i) (y + periodicShift n k) + Util n v i j (y + periodicShift n k)
        = pderiv i (Ftil n v j) y + pderiv j (Ftil n v i) y + Util n v i j y
      rw [(hFj.pderiv i).periodic y k, (hFi.pderiv j).periodic y k, hUij.periodic y k]
  have hLc := smoothPeriodic_ofReal_scalar hL
  have hRc := smoothPeriodic_ofReal_scalar hR
  have hc1 : Continuous (fun y => ((pderiv i (Ftil n v j) y : ℝ) : ℂ)) :=
    continuous_ofReal_of_contDiff (pderiv_contDiff hFj.smooth i)
  have hc2 : Continuous (fun y => ((pderiv j (Ftil n v i) y : ℝ) : ℂ)) :=
    continuous_ofReal_of_contDiff (pderiv_contDiff hFi.smooth j)
  have hc3 : Continuous (fun y => ((Util n v i j y : ℝ) : ℂ)) :=
    continuous_ofReal_of_contDiff hUij.smooth
  have hc12 : Continuous (fun y => ((pderiv i (Ftil n v j) y : ℝ) : ℂ)
      + ((pderiv j (Ftil n v i) y : ℝ) : ℂ)) := hc1.add hc2
  have hadd1 := stdFourierCoeff_add hc12 hc3
  have hadd2 := stdFourierCoeff_add hc1 hc2
  have hcoeff : stdFourierCoeff n
        (fun y => ((pderiv i (vsynth n v) y ⬝ᵥ pderiv j (vsynth n v) y : ℝ) : ℂ))
      = stdFourierCoeff n
        (fun y => ((pderiv i (Ftil n v j) y + pderiv j (Ftil n v i) y
          + Util n v i j y : ℝ) : ℂ)) := by
    rw [stdFourierCoeff_dotProduct hn (hVsp.pderiv i) (hVsp.pderiv j),
      vcoeff_pderiv hn hVsp i, vcoeff_pderiv hn hVsp j, vcoeff_vsynth hn hv hr,
      dotConv_eq_Fb_Ub hn hv hr i j]
    have hcast : (fun y => ((pderiv i (Ftil n v j) y + pderiv j (Ftil n v i) y
          + Util n v i j y : ℝ) : ℂ))
        = fun y => (((pderiv i (Ftil n v j) y : ℝ) : ℂ) + ((pderiv j (Ftil n v i) y : ℝ) : ℂ))
            + ((Util n v i j y : ℝ) : ℂ) := by
      funext y; push_cast; ring
    rw [hcast, hadd1, hadd2,
      stdFourierCoeff_pderiv_ofReal hn hFj i, stdFourierCoeff_pderiv_ofReal hn hFi j,
      coeff_Ftil hn hv hr i, coeff_Ftil hn hv hr j, coeff_Util hn hv hr i j]
  have hx := congrFun (eq_of_stdFourierCoeff_eq hn hLc.1 hLc.2 hRc.1 hRc.2 hcoeff) x
  exact_mod_cast hx

/-! ## The ansatz from the dual frame -/

/-- `W · ∂ᵢu₀ = -F_tildeᵢ`. -/
lemma Wfun_dot_pderiv {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hfree : IsFree u₀)
    (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : VecSeq n N) (i : Fin n) (x : Fin n → ℝ) :
    Wfun n u₀ h v x ⬝ᵥ pderiv i u₀ x = -Ftil n v i x := by
  have hd := dualFrame_dotProduct hfree
  have hA : ∀ k, dualA u₀ k x ⬝ᵥ pderiv i u₀ x = if k = i then 1 else 0 := fun k => by
    have := hd (Sum.inl k) (Sum.inl i) x
    simpa [dualA, frame] using this
  have hB : ∀ pq ∈ pairs n, dualB u₀ pq.1 pq.2 x ⬝ᵥ pderiv i u₀ x = 0 := fun pq hpq => by
    have hle : pq.1 ≤ pq.2 := (Finset.mem_filter.mp hpq).2
    have := hd (Sum.inr ⟨pq, hle⟩) (Sum.inl i) x
    simp only [frame, reduceCtorEq, ite_false] at this
    simp [dualB, hle, this]
  unfold Wfun
  rw [add_dotProduct, neg_dotProduct, sum_dotProduct, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, hA, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_eq_zero (fun pq hpq => by rw [hB pq hpq, mul_zero]), add_zero]

/-- `W · ∂ₚ∂_q u₀ = ½(U_tilde_{pq} - h_{pq})` for `p ≤ q`. -/
lemma Wfun_dot_pderiv_pderiv {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hfree : IsFree u₀)
    (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : VecSeq n N) {p q : Fin n} (hpq : p ≤ q)
    (x : Fin n → ℝ) :
    Wfun n u₀ h v x ⬝ᵥ pderiv p (pderiv q u₀) x = (1 / 2 : ℝ) * (Util n v p q x - h x p q) := by
  have hd := dualFrame_dotProduct hfree
  have hA : ∀ k, dualA u₀ k x ⬝ᵥ pderiv p (pderiv q u₀) x = 0 := fun k => by
    have := hd (Sum.inl k) (Sum.inr ⟨(p, q), hpq⟩) x
    simpa [dualA, frame] using this
  have hB : ∀ pq ∈ pairs n, dualB u₀ pq.1 pq.2 x ⬝ᵥ pderiv p (pderiv q u₀) x
      = if pq = (p, q) then 1 else 0 := fun pq hpq' => by
    have hle : pq.1 ≤ pq.2 := (Finset.mem_filter.mp hpq').2
    have := hd (Sum.inr ⟨pq, hle⟩) (Sum.inr ⟨(p, q), hpq⟩) x
    simp only [frame, Sum.inr.injEq, Subtype.mk.injEq] at this
    simp [dualB, hle, this]
  have hmem : (p, q) ∈ pairs n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩
  unfold Wfun
  rw [add_dotProduct, neg_dotProduct, sum_dotProduct, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, hA, mul_zero, Finset.sum_const_zero, neg_zero, zero_add]
  rw [Finset.sum_congr rfl fun pq hpq' => by rw [hB pq hpq']]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (pairs n) (p, q)]
  simp [hmem]

/-- `∂ᵢ(-f) = -∂ᵢf` for smooth scalar `f`. -/
lemma pderiv_neg (f : (Fin n → ℝ) → ℝ) (i : Fin n) :
    pderiv i (fun y => -f y) = fun y => -pderiv i f y := by
  funext y
  unfold pderiv
  rw [fderiv_fun_neg]
  simp

/-! ## Theorem B -/

/-- **Theorem B.** -/
theorem gunther_perturbation (hn : 0 < n) {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u₀)
    (hfree : IsFree u₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ, SmoothPeriodic h →
      (∀ x, (h x).IsSymm) → hSize n h < ε →
      ∃ v : (Fin n → ℝ) → (Fin N → ℝ), SmoothPeriodic v ∧
        ∀ (x : Fin n → ℝ) (i j : Fin n),
          pderiv i (u₀ + v) x ⬝ᵥ pderiv j (u₀ + v) x = pderiv i u₀ x ⬝ᵥ pderiv j u₀ x + h x i j
              := by
  -- constants from the tame estimates (they depend on `u₀` only: the data `a, b`)
  set r := bLevel n with hr_def
  have hr2 : 1 + (n : ℝ) / 2 < (r : ℝ) - 2 := bLevel_gt n
  -- the data without `h` are used for the constants; `gBTop`/`gBLow`/`gA` do not read `d.h`
  set d₀ : GuntherData n N := bData n u₀ 0 with hd₀
  set A : ℝ := gA n N r d₀ with hA_def
  set A' : ℝ := gBTop n N r d₀ with hA'_def
  set ρ : ℝ := 1 / (16 * A + 8 * A' + 1) with hρ_def
  have hd₀s : d₀.Smooth := bData_smooth hn hu hfree ⟨contDiff_const, fun _ _ => rfl⟩
  have hIter₀ := gunther_iterHyp hn hr2 d₀ hd₀s
  have hA0 : 0 ≤ A := hIter₀.A_nonneg
  have hA'0 : 0 ≤ A' := hIter₀.A'_nonneg
  have hρ : 0 < ρ := by rw [hρ_def]; positivity
  have hAρ : 4 * A * ρ ≤ 1 / 4 := by
    rw [hρ_def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hA'ρ : 4 * A' * ρ ≤ 1 / 2 := by
    rw [hρ_def, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨ρ / (4 * cConst n N u₀ + 1), by have := cConst_nonneg (n := n) (N := N) u₀; positivity,
    fun h hh hsymm hsmall => ?_⟩
  -- the data with `h`
  set d : GuntherData n N := bData n u₀ h with hd
  have hds : d.Smooth := bData_smooth hn hu hfree hh
  have hdr : d.Real := bData_real hh
  have hIter : IterHyp n N r (gC d) (gB d) (gA n N r d) (gBTop n N r d) (gBLow n N r d) :=
    gunther_iterHyp hn hr2 d hds
  -- the constants of `d` agree with those of `d₀` (they only involve `a`, `b`)
  have hAeq : gA n N r d = A := rfl
  have hA'eq : gBTop n N r d = A' := rfl
  rw [hAeq, hA'eq] at hIter
  -- smallness of the constant term
  have hc : 4 * vecNormSq n N r (gC d) ≤ ρ := by
    have h1 := gC_bound hn hu hfree hh
    have h2 := cConst_nonneg (n := n) (N := N) u₀
    have h3 := hSize_nonneg (n := n) h
    have h4 : cConst n N u₀ * hSize n h ≤ cConst n N u₀ * (ρ / (4 * cConst n N u₀ + 1)) :=
      mul_le_mul_of_nonneg_left hsmall.le h2
    have h5 : 4 * (cConst n N u₀ * (ρ / (4 * cConst n N u₀ + 1))) ≤ ρ := by
      have hpos : 0 < 4 * cConst n N u₀ + 1 := by positivity
      have : cConst n N u₀ * (ρ / (4 * cConst n N u₀ + 1)) ≤ ρ / 4 := by
        rw [← mul_div_assoc, div_le_iff₀ hpos]; nlinarith
      linarith
    linarith
  -- the fixed point
  obtain ⟨v, hvmem, hvfix, -, hvreal⟩ := exists_fixed_point hIter hρ hAρ hA'ρ hc VReal vreal_zero
    (fun v hv => vreal_gT hdr hv) (fun u a hu hlim => vreal_of_tendsto hu hlim)
  have hvrapid : VRapid n N v := vrapid_of_vmem hvmem
  -- its synthesis
  set V := vsynth n v with hV
  have hVsp : SmoothPeriodic V := vsynth_smoothPeriodic hn hvrapid
  refine ⟨V, hVsp, ?_⟩
  -- `V = W` by comparing coefficients
  have hVW : V = Wfun n u₀ h v := by
    have h1 : vcoeff n V = vcoeff n (Wfun n u₀ h v) := by
      rw [hV, vcoeff_vsynth hn hvrapid hvreal, vcoeff_Wfun hn hu hfree hh hvrapid hvreal, ← hvfix]
    have h2 := congrArg (vsynth n) h1
    rwa [vsynth_vcoeff hn hVsp, vsynth_vcoeff hn (Wfun_smoothPeriodic hn hu hfree hh hvrapid)] at h2
  -- the ansatz, pointwise
  have hans1 : ∀ i x, V x ⬝ᵥ pderiv i u₀ x = -Ftil n v i x := by
    intro i x; rw [hVW]; exact Wfun_dot_pderiv hfree h v i x
  have hans2 : ∀ i j x, V x ⬝ᵥ pderiv i (pderiv j u₀) x = (1 / 2 : ℝ) * (Util n v i j x - h x i
      j) := by
    intro i j x
    rcases le_or_gt i j with hij | hij
    · rw [hVW]; exact Wfun_dot_pderiv_pderiv hfree h v hij x
    · rw [pderiv_comm hu.smooth i j, hVW, Wfun_dot_pderiv_pderiv hfree h v hij.le x,
        Util_symm j i, (hsymm x).apply j i]
  -- the product identity
  have hprod := pderiv_dot_pderiv_vsynth hn hvrapid hvreal
  -- assemble
  intro x i j
  have hVs := hVsp.smooth
  have hus := hu.smooth
  -- `∂ᵢ(u₀ + V) = ∂ᵢu₀ + ∂ᵢV`
  have hdi : pderiv i (u₀ + V) x = pderiv i u₀ x + pderiv i V x := by
    change pderiv i (fun y => u₀ y + V y) x = _
    rw [pderiv_add hus hVs]
  have hdj : pderiv j (u₀ + V) x = pderiv j u₀ x + pderiv j V x := by
    change pderiv j (fun y => u₀ y + V y) x = _
    rw [pderiv_add hus hVs]
  -- product rule: `∂ᵢ(V · ∂ⱼu₀) = ∂ᵢV · ∂ⱼu₀ + V · ∂ᵢ∂ⱼu₀`
  have hpr_i : pderiv i (fun y => V y ⬝ᵥ pderiv j u₀ y) x
      = pderiv i V x ⬝ᵥ pderiv j u₀ x + V x ⬝ᵥ pderiv i (pderiv j u₀) x :=
    pderiv_dotProduct hVs (pderiv_contDiff hus j) i x
  have hpr_j : pderiv j (fun y => V y ⬝ᵥ pderiv i u₀ y) x
      = pderiv j V x ⬝ᵥ pderiv i u₀ x + V x ⬝ᵥ pderiv j (pderiv i u₀) x :=
    pderiv_dotProduct hVs (pderiv_contDiff hus i) j x
  -- `V · ∂ⱼu₀ = -F_tildeⱼ` as functions, hence for their derivatives
  have hfun_j : (fun y => V y ⬝ᵥ pderiv j u₀ y) = fun y => -Ftil n v j y := funext fun y =>
      hans1 j y
  have hfun_i : (fun y => V y ⬝ᵥ pderiv i u₀ y) = fun y => -Ftil n v i y := funext fun y =>
      hans1 i y
  rw [hfun_j, pderiv_neg (Ftil n v j)] at hpr_i
  rw [hfun_i, pderiv_neg (Ftil n v i)] at hpr_j
  simp only at hpr_i hpr_j
  rw [hans2 i j x] at hpr_i
  rw [hans2 j i x, Util_symm j i, (hsymm x).apply i j] at hpr_j
  -- expand and finish
  rw [hdi, hdj, add_dotProduct, dotProduct_add, dotProduct_add, hprod i j x]
  have hcomm : pderiv i u₀ x ⬝ᵥ pderiv j V x = pderiv j V x ⬝ᵥ pderiv i u₀ x := dotProduct_comm _ _
  rw [hcomm]
  linarith [hpr_i, hpr_j]

end NashEmbedding

end
