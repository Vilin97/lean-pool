/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportODEApplications
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Composition
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Gronwall

/-!
# The lower-order Faà di Bruno term in the flow induction

This module isolates the one-block term in the ordered-finpartition chain
rule.  The remaining terms are bounded by the all-order 10421 resummation,
with the paper's coefficient and radius factors.
-/

@[expose] public section

noncomputable section

namespace AVenhance.FaaDiBruno

open FormalMultilinearSeries
open Homogenization
open MeasureTheory
open scoped ContDiff

/-- The unique ordered finpartition with one block. -/
def Remainder.flowSingleBlock {n : ℕ} (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize := fun _ => n
  partSize_pos _ := hn
  emb := fun _ j => j
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint := by
    intro i hi j hj hij
    have h : i = j := Subsingleton.elim _ _
    exact (hij h).elim
  cover := by
    intro x
    exact ⟨0, x, rfl⟩

theorem Remainder.flowSingleBlock_unique {n : ℕ} (hn : 0 < n)
    (c : OrderedFinpartition n) (hc : c.length = 1) :
    c = Remainder.flowSingleBlock hn := by
  rcases c with ⟨len, psize, hpos, emb, hem, hparts, hdisj, hcover⟩
  change len = 1 at hc
  subst len
  have hcard : Fintype.card (Σ i : Fin 1, Fin (psize i)) = n := by
    calc
      _ = Fintype.card (Fin n) := Fintype.card_congr
        (OrderedFinpartition.equivSigma ⟨1, psize, hpos, emb, hem, hparts, hdisj, hcover⟩)
      _ = n := Fintype.card_fin n
  have hsize : psize 0 = n := by simpa using hcard
  have hp : psize = fun _ : Fin 1 => n := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hsize
  subst psize
  have hemb : emb 0 = _root_.id := StrictMono.eq_id (hem 0)
  refine OrderedFinpartition.ext rfl ?_ ?_
  · exact HEq.rfl
  · have hemb' : emb = fun _ : Fin 1 => (_root_.id : Fin n → Fin n) := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hemb
    exact heq_of_eq hemb'

theorem Remainder.flowSingleBlock_compAlong_apply {n : ℕ} (hn : 0 < n)
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : FormalMultilinearSeries ℝ F G) (p : FormalMultilinearSeries ℝ E F)
    (v : Fin n → E) :
    (q.compAlongOrderedFinpartition p (Remainder.flowSingleBlock hn)) v =
      q 1 (fun _ : Fin 1 => p n v) := by
  change (q 1) (fun _ : Fin 1 => p n (v ∘ fun j => j)) =
    q 1 (fun _ : Fin 1 => p n v)
  congr 1

theorem Remainder.flowPartSize_sum {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i : Fin c.length, c.partSize i = n := by
  calc
    ∑ i : Fin c.length, c.partSize i =
        Fintype.card (Σ i : Fin c.length, Fin (c.partSize i)) := by
          simp [Fintype.card_sigma]
    _ = Fintype.card (Fin n) := Fintype.card_congr c.equivSigma
    _ = n := Fintype.card_fin n

theorem Remainder.flowOneAddSum_le_prodAddOne {α : Type*} (s : Finset α)
    (f : α → ℕ) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (f i + 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hlocal : 1 + f a + (∑ i ∈ s, f i) ≤
          (f a + 1) * (1 + ∑ i ∈ s, f i) := by
        nlinarith [Nat.zero_le (f a * (∑ i ∈ s, f i))]
      simpa [Nat.add_assoc] using hlocal.trans (Nat.mul_le_mul_left (f a + 1) ih)

theorem Remainder.flowShiftFactor {n : ℕ} (hn : 0 < n)
    (c : OrderedFinpartition n) :
    (n + 1 : ℝ) ^ 2 ≤ (c.length + 1 : ℝ) ^ 2 *
      ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2 := by
  have hsum := Remainder.flowPartSize_sum c
  have hprodNat : n + 1 ≤ ∏ i : Fin c.length, (c.partSize i + 1) := by
    have h := Remainder.flowOneAddSum_le_prodAddOne Finset.univ c.partSize
    rw [hsum] at h
    omega
  have hprodReal : (n + 1 : ℝ) ≤
      (c.length + 1 : ℝ) * ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) := by
    have hprodReal' : (n + 1 : ℝ) ≤
        ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) := by
      exact_mod_cast hprodNat
    calc
      _ ≤ 1 * ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) := by simpa using hprodReal'
      _ ≤ (c.length + 1 : ℝ) * ∏ i : Fin c.length,
          (c.partSize i + 1 : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ (n + 1 : ℝ))
      (by positivity : 0 ≤ (c.length + 1 : ℝ) *
        ∏ i : Fin c.length, (c.partSize i + 1 : ℝ))).2 hprodReal
  calc
    (n + 1 : ℝ) ^ 2 ≤
        ((c.length + 1 : ℝ) * ∏ i : Fin c.length,
          (c.partSize i + 1 : ℝ)) ^ 2 := hsquare
    _ = (c.length + 1 : ℝ) ^ 2 *
        ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2 := by
      rw [mul_pow, Finset.prod_pow]

/-- The positive coefficient weight corresponding to an ordered
finpartition in the flow induction. -/
def flowPositivePartitionWeight {n : ℕ}
    (c : OrderedFinpartition n) : ℝ :=
  (c.length.factorial : ℝ) *
    ∏ i : Fin c.length,
      ((c.partSize i).factorial : ℝ) *
        flowHalfBinomialCoeff (c.partSize i - 1)

theorem flowHalfCoeff_nonneg_of_posSize {r : ℕ} (hr : 1 ≤ r) :
    0 ≤ flowHalfBinomialCoeff (r - 1) := by
  by_cases h : r = 1
  · subst r
    norm_num [flowHalfBinomialCoeff]
  · have hn : 1 ≤ r - 1 := by omega
    exact flowHalfBinomialCoeff_nonneg hn

theorem Remainder.flowHalfBinomialBlockWeight_eq_signedPositive (r : ℕ)
    (hr : 1 ≤ r) :
    orderedPartitionHalfBinomialBlockWeight r =
      (-1 : ℝ) ^ (r - 1) * (r.factorial : ℝ) *
        flowHalfBinomialCoeff (r - 1) := by
  have hsub : r - 1 + 1 = r := Nat.sub_add_cancel hr
  rw [flowHalfBinomialCoeff, hsub]
  unfold orderedPartitionHalfBinomialBlockWeight
  have hpow : (-1 : ℝ) ^ (r - 1) * (-1 : ℝ) ^ (r - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (r.factorial : ℝ) * Ring.choose (1 / 2 : ℝ) r =
        ((-1 : ℝ) ^ (r - 1) * (-1 : ℝ) ^ (r - 1)) *
          ((r.factorial : ℝ) * Ring.choose (1 / 2 : ℝ) r) := by rw [hpow, one_mul]
    _ = _ := by ring

theorem Remainder.flowSignedPartitionWeight_eq_positive {n : ℕ}
    (c : OrderedFinpartition n) :
    (-1 : ℝ) ^ n * orderedPartitionHalfBinomialWeight c =
      flowPositivePartitionWeight c := by
  have hr : ∀ i : Fin c.length, 1 ≤ c.partSize i :=
    fun i => Nat.succ_le_iff.mpr (c.partSize_pos i)
  have hblocks :
      (∏ i : Fin c.length,
        orderedPartitionHalfBinomialBlockWeight (c.partSize i)) =
      (∏ i : Fin c.length, (-1 : ℝ) ^ (c.partSize i - 1)) *
        ∏ i : Fin c.length,
          ((c.partSize i).factorial : ℝ) *
            flowHalfBinomialCoeff (c.partSize i - 1) := by
    calc
      _ = ∏ i : Fin c.length,
          ((-1 : ℝ) ^ (c.partSize i - 1) *
            ((c.partSize i).factorial : ℝ) *
              flowHalfBinomialCoeff (c.partSize i - 1)) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact Remainder.flowHalfBinomialBlockWeight_eq_signedPositive _ (hr i)
      _ = ∏ i : Fin c.length,
          ((-1 : ℝ) ^ (c.partSize i - 1) *
            (((c.partSize i).factorial : ℝ) *
              flowHalfBinomialCoeff (c.partSize i - 1))) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
      _ = (∏ i : Fin c.length, (-1 : ℝ) ^ (c.partSize i - 1)) *
          ∏ i : Fin c.length,
            ((c.partSize i).factorial : ℝ) *
              flowHalfBinomialCoeff (c.partSize i - 1) := by
            rw [Finset.prod_mul_distrib]
  have hsignSumNat :
      (∑ i : Fin c.length, (c.partSize i - 1)) + c.length = n := by
    have hsizes := Remainder.flowPartSize_sum c
    calc
      (∑ i : Fin c.length, (c.partSize i - 1)) + c.length =
          ∑ i : Fin c.length, ((c.partSize i - 1) + 1) := by
        calc
          _ = (∑ i : Fin c.length, (c.partSize i - 1)) +
              ∑ i : Fin c.length, (1 : ℕ) := by simp
          _ = _ := (Finset.sum_add_distrib).symm
      _ = ∑ i : Fin c.length, c.partSize i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Nat.sub_add_cancel (hr i)
      _ = n := hsizes
  have hsignSum :
      (∑ i : Fin c.length, (c.partSize i - 1) : ℕ) + c.length = n := hsignSumNat
  change (-1 : ℝ) ^ n *
      ((-1 : ℝ) ^ c.length * (c.length.factorial : ℝ) *
        ∏ i : Fin c.length,
          orderedPartitionHalfBinomialBlockWeight (c.partSize i)) =
    (c.length.factorial : ℝ) *
      ∏ i : Fin c.length,
        ((c.partSize i).factorial : ℝ) *
          flowHalfBinomialCoeff (c.partSize i - 1)
  rw [hblocks, Finset.prod_pow_eq_pow_sum]
  calc
    _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ c.length *
        (-1 : ℝ) ^ (∑ i : Fin c.length, (c.partSize i - 1))) *
        (c.length.factorial : ℝ) *
          ∏ i : Fin c.length,
            ((c.partSize i).factorial : ℝ) *
              flowHalfBinomialCoeff (c.partSize i - 1) := by ring
    _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        (c.length.factorial : ℝ) *
          ∏ i : Fin c.length,
            ((c.partSize i).factorial : ℝ) *
              flowHalfBinomialCoeff (c.partSize i - 1) := by
        have hexp : n + c.length +
            (∑ i : Fin c.length, (c.partSize i - 1)) = n + n := by
          omega
        have hsign : (-1 : ℝ) ^ (n + c.length) *
            (-1 : ℝ) ^ (∑ i : Fin c.length, (c.partSize i - 1)) =
              (-1 : ℝ) ^ n * (-1 : ℝ) ^ n := by
          calc
            _ = (-1 : ℝ) ^ (n + c.length +
                (∑ i : Fin c.length, (c.partSize i - 1))) := by
                  rw [← pow_add]
            _ = (-1 : ℝ) ^ (n + n) := by rw [hexp]
            _ = (-1 : ℝ) ^ n * (-1 : ℝ) ^ n := by rw [← pow_add]
        calc
          _ = ((-1 : ℝ) ^ (n + c.length) *
              (-1 : ℝ) ^ (∑ i : Fin c.length, (c.partSize i - 1))) *
                (c.length.factorial : ℝ) *
                  ∏ i : Fin c.length,
                    ((c.partSize i).factorial : ℝ) *
                      flowHalfBinomialCoeff (c.partSize i - 1) := by ring
          _ = _ := by rw [hsign]
    _ = _ := by
      rw [← mul_pow]
      norm_num

/-- The positive form of the 10421 resummation. Each summand is the absolute
value of the signed paper summand, written with the positive coefficients
`flowHalfBinomialCoeff`; this form is convenient for bounding the lower-order
Faà di Bruno terms. -/
theorem orderedFinpartitionPositiveHalfBinomialResummation10421
    (n : ℕ) :
    ∑ c : OrderedFinpartition n, flowPositivePartitionWeight c =
      2 * ((n + 1).factorial : ℝ) * flowHalfBinomialCoeff n := by
  calc
    ∑ c : OrderedFinpartition n, flowPositivePartitionWeight c =
        ∑ c : OrderedFinpartition n,
          (-1 : ℝ) ^ n * orderedPartitionHalfBinomialWeight c := by
            apply Finset.sum_congr rfl
            intro c hc
            exact (Remainder.flowSignedPartitionWeight_eq_positive c).symm
    _ = (-1 : ℝ) ^ n * orderedPartitionHalfBinomialSum n := by
          change (∑ c : OrderedFinpartition n,
              (-1 : ℝ) ^ n * orderedPartitionHalfBinomialWeight c) =
            (-1 : ℝ) ^ n *
              (∑ c : OrderedFinpartition n, orderedPartitionHalfBinomialWeight c)
          rw [← Finset.mul_sum]
    _ = 2 * ((n + 1).factorial : ℝ) * flowHalfBinomialCoeff n := by
          rw [orderedFinpartitionResummation10421]
          simp only [flowHalfBinomialCoeff]
          ring

theorem Remainder.flowVecOneEquivSymm_norm_le :
    ‖(vecOneEquiv 2).symm.toContinuousLinearMap‖ ≤ 2 := by
  let L : Vec 2 →L[ℝ] VecOne 2 := (vecOneEquiv 2).symm.toContinuousLinearMap
  refine ContinuousLinearMap.opNorm_le_bound L (by norm_num) fun x ↦ ?_
  calc
    ‖L x‖ = ∑ i : Fin 2, ‖(L x) i‖ := by rw [PiLp.norm_eq_of_L1]
    _ ≤ ∑ _i : Fin 2, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hcoord : (L x) i = x i := rfl
      rw [hcoord, Pi.norm_def]
      change (‖x i‖₊ : ℝ) ≤ _
      exact Finset.le_sup (s := Finset.univ)
        (f := fun j : Fin 2 ↦ ‖x j‖₊) (Finset.mem_univ i)
    _ = (2 : ℝ) * ‖x‖ := by simp [Finset.sum_const, nsmul_eq_mul]

theorem Remainder.flowContDiffLiftVecOneTop {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec 2 → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (liftVecOne f) := by
  dsimp [liftVecOne]
  exact hf.comp_continuousLinearMap
    (g := (vecOneEquiv 2).toContinuousLinearMap)

theorem Remainder.flowContDiffLiftVecOneEndoTop (F : Vec 2 → Vec 2)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (liftVecOneEndo F) := by
  let L : Vec 2 →L[ℝ] VecOne 2 := (vecOneEquiv 2).symm.toContinuousLinearMap
  have hLift : ContDiff ℝ ∞ (liftVecOne F) := Remainder.flowContDiffLiftVecOneTop F hF
  simpa [liftVecOneEndo, liftVecOne, L] using L.contDiff.comp hLift

theorem Remainder.flowLiftEndoDerivativeBound
    {m r : ℕ} (F : Vec 2 → Vec 2) (hF : ContDiff ℝ m F) (hr : r ≤ m)
    {C R : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hFsnorm : snorm F r R ≤ ENNReal.ofReal C) (x : Vec 2) :
    ‖iteratedFDeriv ℝ r (liftVecOneEndo F) (WithLp.toLp 1 x)‖ ≤
      2 * (C * r.factorial * R ^ r / (r + 1 : ℝ) ^ 2) := by
  let L : Vec 2 →L[ℝ] VecOne 2 := (vecOneEquiv 2).symm.toContinuousLinearMap
  let T := iteratedFDeriv ℝ r (liftVecOne F) (WithLp.toLp 1 x)
  have hT := compositionDerivative_norm_le_of_snorm_le F hF hr hR hC hFsnorm x
  have hcomp := L.iteratedFDeriv_comp_left
    (contDiff_liftVecOne hF).contDiffAt (i := r) (by exact_mod_cast hr)
      (x := WithLp.toLp 1 x)
  have hcomp' :
      iteratedFDeriv ℝ r (liftVecOneEndo F) (WithLp.toLp 1 x) =
        L.compContinuousMultilinearMap T := by
    simpa [liftVecOneEndo, liftVecOne, L, T, Function.comp_def] using hcomp
  calc
    ‖iteratedFDeriv ℝ r (liftVecOneEndo F) (WithLp.toLp 1 x)‖ =
        ‖L.compContinuousMultilinearMap T‖ := by rw [hcomp']
    _ ≤ ‖L‖ * ‖T‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le L T
    _ ≤ 2 * (C * r.factorial * R ^ r / (r + 1 : ℝ) ^ 2) :=
      mul_le_mul (by simpa [L] using Remainder.flowVecOneEquivSymm_norm_le) hT
        (norm_nonneg _) (by positivity)

theorem Remainder.flowInnerCoefficientProduct {n : ℕ}
    (c : OrderedFinpartition n) (A : Fin c.length → ℝ)
    (Rf Rflow : ℝ) :
    ∏ i : Fin c.length,
        (A i / Rf * (c.partSize i).factorial *
          Rflow ^ c.partSize i / (c.partSize i + 1 : ℝ) ^ 2) =
      (∏ i : Fin c.length, A i * (c.partSize i).factorial) * Rflow ^ n /
        (Rf ^ c.length *
          ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2) := by
  have hpow : ∏ i : Fin c.length, Rflow ^ c.partSize i = Rflow ^ n := by
    rw [Finset.prod_pow_eq_pow_sum, Remainder.flowPartSize_sum]
  have hnum :
      ∏ i : Fin c.length,
        (A i * (c.partSize i).factorial * Rflow ^ c.partSize i) =
      (∏ i : Fin c.length, A i * (c.partSize i).factorial) * Rflow ^ n := by
    calc
      _ = (∏ i : Fin c.length, A i * (c.partSize i).factorial) *
          ∏ i : Fin c.length, Rflow ^ c.partSize i := by
        rw [Finset.prod_mul_distrib]
      _ = _ := by rw [hpow]
  have hden :
      ∏ i : Fin c.length,
        (Rf * (c.partSize i + 1 : ℝ) ^ 2) =
      Rf ^ c.length *
        ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  calc
    _ = ∏ i : Fin c.length,
          ((A i * (c.partSize i).factorial * Rflow ^ c.partSize i) /
            (Rf * (c.partSize i + 1 : ℝ) ^ 2)) := by
      apply Finset.prod_congr rfl
      intro i hi
      field_simp
    _ = (∏ i : Fin c.length,
          (A i * (c.partSize i).factorial * Rflow ^ c.partSize i)) /
        ∏ i : Fin c.length, (Rf * (c.partSize i + 1 : ℝ) ^ 2) := by
      rw [Finset.prod_div_distrib]
    _ = _ := by rw [hnum, hden]

theorem Remainder.flowPartSize_lt_of_length_ge_two {n : ℕ}
    (c : OrderedFinpartition n) (hlen : 2 ≤ c.length) (i : Fin c.length) :
    c.partSize i < n := by
  have hother : ∃ j : Fin c.length, j ≠ i := by
    have hcard : 1 < (Finset.univ : Finset (Fin c.length)).card := by
      simp only [Finset.card_univ, Fintype.card_fin]
      exact hlen
    obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hcard
    by_cases hai : a = i
    · exact ⟨b, fun hbi => hab (hai.trans hbi.symm)⟩
    · exact ⟨a, hai⟩
  obtain ⟨j, hji⟩ := hother
  have hsum := Remainder.flowPartSize_sum c
  have herase :
      (∑ k ∈ (Finset.univ : Finset (Fin c.length)).erase i, c.partSize k) +
          c.partSize i = n := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin c.length))
      c.partSize (Finset.mem_univ i)
    simpa [hsum] using h
  have hpositive :
      0 < ∑ k ∈ (Finset.univ : Finset (Fin c.length)).erase i,
          c.partSize k := by
    apply Finset.sum_pos
    · intro k hk
      exact c.partSize_pos k
    · exact ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩⟩
  omega

theorem Remainder.flowFaaTerm_bound
    {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2))
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hB : ∀ t k, 1 ≤ k → k ≤ N →
      snorm (b t) k R_f ≤ ENNReal.ofReal C_f)
    (t : ℝ) (x : Vec 2)
    (hDn : ∀ k, 1 ≤ k → k < n →
      snorm (fun y => X t y 0) k
        (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)) ≤
          ENNReal.ofReal (flowHalfBinomialCoeff (k - 1) / (2 * R_f)))
    (c : OrderedFinpartition n) (hc : 2 ≤ c.length) :
    ‖(ftaylorSeries ℝ (liftVecOne (b t))
          ((liftVecOneEndo (fun y => X t y 0)) (WithLp.toLp 1 x))).compAlongOrderedFinpartition
        (ftaylorSeries ℝ (liftVecOneEndo (fun y => X t y 0))
          (WithLp.toLp 1 x)) c‖ ≤
      (C_f *
          (8 * 2 * R_f *
            (1 + (8 * 2 * C_f * R_f) * |t|)) ^ n /
          (n + 1 : ℝ) ^ 2) * flowPositivePartitionWeight c := by
  let F : Vec 2 → Vec 2 := fun y => X t y 0
  let H : VecOne 2 → Vec 2 := liftVecOne (b t)
  let G : VecOne 2 → VecOne 2 := liftVecOneEndo F
  let y : VecOne 2 := WithLp.toLp 1 x
  let Rflow : ℝ := 8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)
  let common : ℝ := C_f * Rflow ^ n / (n + 1 : ℝ) ^ 2
  have hRflow : 0 < Rflow := by dsimp [Rflow]; positivity
  have hF : ContDiff ℝ ∞ F := by
    have hmap : ContDiff ℝ ∞ (fun z : Vec 2 => ((t, z), (0 : ℝ))) := by fun_prop
    exact hXsmooth.comp hmap
  have hbSlice : ContDiff ℝ ∞ (b t) := by
    have hmap : ContDiff ℝ ∞ (fun z : Vec 2 => (t, z)) := by fun_prop
    exact hb.smooth.comp hmap
  have hH : ContDiff ℝ ∞ H := Remainder.flowContDiffLiftVecOneTop (b t) hbSlice
  have hG : ContDiff ℝ ∞ G := Remainder.flowContDiffLiftVecOneEndoTop F hF
  have hOuter (s : ℕ) (hspos : 1 ≤ s) (hs : s ≤ n) :
      ‖iteratedFDeriv ℝ s H (G y)‖ ≤
        C_f * s.factorial * R_f ^ s / (s + 1 : ℝ) ^ 2 := by
    have hsN : s ≤ N := hs.trans hnN
    have hbound := compositionDerivative_norm_le_of_snorm_le
      (b t) (hbSlice.of_le (by simp)) hsN hRf (le_of_lt hCf)
        (hB t s hspos hsN)
        ((vecOneEquiv 2) (G y))
    have hGY : G y = (vecOneEquiv 2).symm (F ((vecOneEquiv 2) y)) := by
      simp [G, F, y, liftVecOneEndo, liftVecOne, vecOneEquiv,
        PiLp.coe_symm_continuousLinearEquiv, PiLp.coe_continuousLinearEquiv]
    have harg (z : Vec 2) :
        WithLp.toLp 1 z = (vecOneEquiv 2).symm z := by
      ext i
      rfl
    simpa [H, G, hGY, liftVecOne, harg] using hbound
  have hInner (i : Fin c.length) :
      ‖iteratedFDeriv ℝ (c.partSize i) G y‖ ≤
        (flowHalfBinomialCoeff (c.partSize i - 1) / R_f) *
          (c.partSize i).factorial * Rflow ^ c.partSize i /
            (c.partSize i + 1 : ℝ) ^ 2 := by
    let r := c.partSize i
    have hrpos : 1 ≤ r := Nat.succ_le_iff.mpr (c.partSize_pos i)
    have hrn : r < n := Remainder.flowPartSize_lt_of_length_ge_two c hc i
    have hA : 0 ≤ flowHalfBinomialCoeff (r - 1) :=
      flowHalfCoeff_nonneg_of_posSize hrpos
    have hDn' := hDn r hrpos hrn
    have hFfinite : ContDiff ℝ r F := hF.of_le (by simp)
    have hbound := Remainder.flowLiftEndoDerivativeBound F hFfinite le_rfl hRflow
      (by positivity : 0 ≤ flowHalfBinomialCoeff (r - 1) / (2 * R_f)) hDn' x
    have hscale : 2 *
        (flowHalfBinomialCoeff (r - 1) / (2 * R_f) * r.factorial *
          Rflow ^ r / (r + 1 : ℝ) ^ 2) =
      flowHalfBinomialCoeff (r - 1) / R_f * r.factorial *
        Rflow ^ r / (r + 1 : ℝ) ^ 2 := by
      field_simp [ne_of_gt hRf]
    simpa [G, y, r] using hbound.trans_eq hscale
  have hOuterC :
      ‖ftaylorSeries ℝ H (G y) c.length‖ ≤
        C_f * c.length.factorial * R_f ^ c.length /
          (c.length + 1 : ℝ) ^ 2 := by
    simpa [ftaylorSeries] using hOuter c.length
      (by omega : 1 ≤ c.length) (OrderedFinpartition.length_le c)
  have hbase :
      ‖(ftaylorSeries ℝ H (G y)).compAlongOrderedFinpartition
          (ftaylorSeries ℝ G y) c‖ ≤
        (C_f * c.length.factorial * R_f ^ c.length /
            (c.length + 1 : ℝ) ^ 2) *
          ∏ i : Fin c.length,
            ((flowHalfBinomialCoeff (c.partSize i - 1) / R_f) *
              (c.partSize i).factorial * Rflow ^ c.partSize i /
                (c.partSize i + 1 : ℝ) ^ 2) := by
    have hcomp := c.norm_compAlongOrderedFinpartition_le
      (ftaylorSeries ℝ H (G y) c.length)
      (fun i => ftaylorSeries ℝ G y (c.partSize i))
    have hprod :
        (∏ i : Fin c.length, ‖ftaylorSeries ℝ G y (c.partSize i)‖) ≤
          ∏ i : Fin c.length,
            ((flowHalfBinomialCoeff (c.partSize i - 1) / R_f) *
              (c.partSize i).factorial * Rflow ^ c.partSize i /
                (c.partSize i + 1 : ℝ) ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact norm_nonneg _
      · intro i hi
        exact hInner i
    have houter0 : 0 ≤ C_f * c.length.factorial * R_f ^ c.length /
        (c.length + 1 : ℝ) ^ 2 := by positivity
    calc
      _ ≤ ‖ftaylorSeries ℝ H (G y) c.length‖ *
          ∏ i : Fin c.length, ‖ftaylorSeries ℝ G y (c.partSize i)‖ := hcomp
      _ ≤ (C_f * c.length.factorial * R_f ^ c.length /
            (c.length + 1 : ℝ) ^ 2) *
          ∏ i : Fin c.length,
            ((flowHalfBinomialCoeff (c.partSize i - 1) / R_f) *
              (c.partSize i).factorial * Rflow ^ c.partSize i /
                (c.partSize i + 1 : ℝ) ^ 2) :=
        mul_le_mul hOuterC hprod (by positivity) houter0
  have hprodEq := Remainder.flowInnerCoefficientProduct c
    (fun i => flowHalfBinomialCoeff (c.partSize i - 1)) R_f Rflow
  have hratioDen : 0 < (c.length + 1 : ℝ) ^ 2 *
      ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2 := by positivity
  have hratio : ((n + 1 : ℝ) ^ 2) /
      ((c.length + 1 : ℝ) ^ 2 *
        ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2) ≤ 1 :=
    (div_le_one₀ hratioDen).2 (Remainder.flowShiftFactor (by omega) c)
  have hcoeff :
      (C_f * c.length.factorial * R_f ^ c.length /
          (c.length + 1 : ℝ) ^ 2) *
        ∏ i : Fin c.length,
          ((flowHalfBinomialCoeff (c.partSize i - 1) / R_f) *
            (c.partSize i).factorial * Rflow ^ c.partSize i /
              (c.partSize i + 1 : ℝ) ^ 2) =
      common * flowPositivePartitionWeight c *
        (((n + 1 : ℝ) ^ 2) /
          ((c.length + 1 : ℝ) ^ 2 *
            ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2)) := by
    rw [hprodEq]
    have hprodOrder :
        (∏ i : Fin c.length,
          flowHalfBinomialCoeff (c.partSize i - 1) *
            (c.partSize i).factorial) =
          ∏ i : Fin c.length,
            (c.partSize i).factorial *
              flowHalfBinomialCoeff (c.partSize i - 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      ring
    rw [hprodOrder]
    dsimp [common, flowPositivePartitionWeight]
    field_simp [ne_of_gt hRf]
  have hweight0 : 0 ≤ flowPositivePartitionWeight c := by
    dsimp [flowPositivePartitionWeight]
    apply mul_nonneg (by positivity)
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (by positivity)
      (flowHalfCoeff_nonneg_of_posSize
        (Nat.succ_le_iff.mpr (c.partSize_pos i)))
  calc
    _ ≤ (C_f * c.length.factorial * R_f ^ c.length /
          (c.length + 1 : ℝ) ^ 2) *
        ∏ i : Fin c.length,
          ((flowHalfBinomialCoeff (c.partSize i - 1) / R_f) *
            (c.partSize i).factorial * Rflow ^ c.partSize i /
              (c.partSize i + 1 : ℝ) ^ 2) := hbase
    _ = common * flowPositivePartitionWeight c *
        (((n + 1 : ℝ) ^ 2) /
          ((c.length + 1 : ℝ) ^ 2 *
            ∏ i : Fin c.length, (c.partSize i + 1 : ℝ) ^ 2)) := hcoeff
    _ ≤ common * flowPositivePartitionWeight c * 1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = common * flowPositivePartitionWeight c := by ring

/-- Pointwise bound for the lower-order part of the differentiated flow
equation. The one-block Faà di Bruno term has been removed exactly; the
remaining terms are summed by the positive 10421 resummation. -/
theorem flowFaaRemainder_coordinate_bound
    {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N)
    {b : ℝ → Vec 2 → Vec 2} (hb : AVenhance.Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hXsmooth : ContDiff ℝ ∞
      (fun p : (ℝ × Vec 2) × ℝ => X p.1.1 p.1.2 p.2))
    {C_f R_f : ℝ} (hCf : 0 < C_f) (hRf : 0 < R_f)
    (hB : ∀ t k, 1 ≤ k → k ≤ N →
      snorm (b t) k R_f ≤ ENNReal.ofReal C_f)
    (t : ℝ) (x : Vec 2)
    (hDn : ∀ k, 1 ≤ k → k < n →
      snorm (fun y => X t y 0) k
        (8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)) ≤
          ENNReal.ofReal (flowHalfBinomialCoeff (k - 1) / (2 * R_f)))
    (I : Fin n → Fin 2) :
    ‖orderedPartial n (fun z => b t (X t z 0)) x I -
        fderiv ℝ (b t) (X t x 0)
          (orderedPartial n (fun z => X t z 0) x I)‖ ≤
      (C_f *
          (8 * 2 * R_f *
            (1 + (8 * 2 * C_f * R_f) * |t|)) ^ n /
          (n + 1 : ℝ) ^ 2) *
        (2 * ((n + 1).factorial : ℝ) * flowHalfBinomialCoeff n) := by
  classical
  let F : Vec 2 → Vec 2 := fun z => X t z 0
  let H : VecOne 2 → Vec 2 := liftVecOne (b t)
  let G : VecOne 2 → VecOne 2 := liftVecOneEndo F
  let y : VecOne 2 := WithLp.toLp 1 x
  let v : Fin n → VecOne 2 := fun j => coordinateVectorOne 2 (I j)
  let W (c : OrderedFinpartition n) :=
    (ftaylorSeries ℝ H (G y)).compAlongOrderedFinpartition
      (ftaylorSeries ℝ G y) c
  let c₁ : OrderedFinpartition n := Remainder.flowSingleBlock (by omega)
  let Q : ContinuousMultilinearMap ℝ (fun _ : Fin n => VecOne 2) (Vec 2) :=
    ∑ z : {c : OrderedFinpartition n // c.length ≠ 1}, W z.1
  let Rflow : ℝ := 8 * 2 * R_f * (1 + (8 * 2 * C_f * R_f) * |t|)
  let common : ℝ := C_f * Rflow ^ n / (n + 1 : ℝ) ^ 2
  have hRflow : 0 < Rflow := by dsimp [Rflow]; positivity
  have hF : ContDiff ℝ ∞ F := by
    have hmap : ContDiff ℝ ∞ (fun z : Vec 2 => ((t, z), (0 : ℝ))) := by fun_prop
    exact hXsmooth.comp hmap
  have hbSlice : ContDiff ℝ ∞ (b t) := by
    have hmap : ContDiff ℝ ∞ (fun z : Vec 2 => (t, z)) := by fun_prop
    exact hb.smooth.comp hmap
  have hH : ContDiff ℝ ∞ H := Remainder.flowContDiffLiftVecOneTop (b t) hbSlice
  have hG : ContDiff ℝ ∞ G := Remainder.flowContDiffLiftVecOneEndoTop F hF
  have hLiftComp :
      liftVecOne (fun z => b t (F z)) = H ∘ G := by
    funext z
    simp [H, G, liftVecOne, liftVecOneEndo]
  have hHn : ContDiff ℝ n H := hH.of_le (by simp)
  have hGn : ContDiff ℝ n G := hG.of_le (by simp)
  have hFaa := multivariateFaaDiBruno (h := H) (g := G) (n := n)
    (hHn.contDiffAt (x := G y)) (hGn.contDiffAt (x := y))
  have hFaaEval :
      orderedPartial n (fun z => b t (F z)) x I =
        ∑ c : OrderedFinpartition n, W c v := by
    have heval := congrArg (fun D => D v) hFaa
    rw [← hLiftComp] at heval
    simpa [orderedPartial, W, H, G, F, y, v, liftVecOne] using heval
  have hOneBlockSubsingleton :
      Subsingleton {c : OrderedFinpartition n // c.length = 1} := by
    refine ⟨fun a b => ?_⟩
    apply Subtype.ext
    calc
      a.1 = c₁ := Remainder.flowSingleBlock_unique (by omega) a.1 a.2
      _ = b.1 := (Remainder.flowSingleBlock_unique (by omega) b.1 b.2).symm
  have hOneBlockSum :
      (∑ z : {c : OrderedFinpartition n // c.length = 1}, W z.1) = W c₁ := by
    exact @Fintype.sum_subsingleton _ _ _ _ hOneBlockSubsingleton
      (fun z => W z.1)
      (⟨c₁, rfl⟩ : {c : OrderedFinpartition n // c.length = 1})
  have hsplitRaw := Fintype.sum_subtype_add_sum_subtype
    (fun c : OrderedFinpartition n => c.length = 1) W
  rw [hOneBlockSum] at hsplitRaw
  have hsplit :
      (∑ c : OrderedFinpartition n, W c) =
        W c₁ + ∑ z : {c : OrderedFinpartition n // c.length ≠ 1}, W z.1 :=
    hsplitRaw.symm
  let E : VecOne 2 →L[ℝ] Vec 2 :=
    (vecOneEquiv 2).toContinuousLinearMap
  let L : Vec 2 →L[ℝ] VecOne 2 :=
    (vecOneEquiv 2).symm.toContinuousLinearMap
  have hGjet :
      iteratedFDeriv ℝ n G y =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ n (liftVecOne F) y) := by
    have hL := L.iteratedFDeriv_comp_left
      (Remainder.flowContDiffLiftVecOneTop F hF).contDiffAt (i := n) (by simp)
        (x := y)
    simpa [G, liftVecOneEndo, liftVecOne, L, Function.comp_def] using hL
  have hEy : E y = x := by
    simp [E, y, vecOneEquiv, PiLp.coe_continuousLinearEquiv]
  have hEGy : E (G y) = F x := by
    simp [E, G, F, y, liftVecOneEndo, liftVecOne, vecOneEquiv,
      PiLp.coe_symm_continuousLinearEquiv, PiLp.coe_continuousLinearEquiv]
  have hHderiv :
      fderiv ℝ H (G y) = (fderiv ℝ (b t) (F x)).comp E := by
    have hchain :=
      ((hbSlice.differentiable (by norm_num) (F x)).hasFDerivAt).comp
        (G y) E.hasFDerivAt
    have hmap : H = fun z => b t (E z) := by
      funext z
      rfl
    simpa [hmap, hEGy, Function.comp_def] using hchain.fderiv
  have hjetValue :
      iteratedFDeriv ℝ n G y v = L (orderedPartial n F x I) := by
    have h := congrArg (fun D => D v) hGjet
    simpa [orderedPartial, F, v, y, liftVecOne, L] using h
  have hTopValue :
      fderiv ℝ H (G y) (iteratedFDeriv ℝ n G y v) =
        fderiv ℝ (b t) (F x) (orderedPartial n F x I) := by
    rw [hjetValue, hHderiv]
    simp [ContinuousLinearMap.comp_apply, E, L]
  have hTopTerm : W c₁ v =
      fderiv ℝ (b t) (F x) (orderedPartial n F x I) := by
    have hsingle := Remainder.flowSingleBlock_compAlong_apply (n := n) (by omega)
      (ftaylorSeries ℝ H (G y)) (ftaylorSeries ℝ G y) v
    have hformula : W c₁ v =
        fderiv ℝ H (G y) (iteratedFDeriv ℝ n G y v) := by
      simpa [W, ftaylorSeries, iteratedFDeriv_one_apply] using hsingle
    exact hformula.trans hTopValue
  have hsumEval :
      (∑ c : OrderedFinpartition n, W c) v =
        W c₁ v + (∑ z : {c : OrderedFinpartition n // c.length ≠ 1}, W z.1) v := by
    have h := congrArg (fun M => M v) hsplit
    simpa [map_sum] using h
  have hFaaEval' :
      orderedPartial n (fun z => b t (F z)) x I =
        (∑ c : OrderedFinpartition n, W c) v := by
    calc
      _ = ∑ c : OrderedFinpartition n, W c v := hFaaEval
      _ = (∑ c : OrderedFinpartition n, W c) v := by simp
  have hdecomp :
      orderedPartial n (fun z => b t (F z)) x I =
        fderiv ℝ (b t) (F x) (orderedPartial n F x I) + Q v := by
    calc
      _ = (∑ c : OrderedFinpartition n, W c) v := hFaaEval'
      _ = W c₁ v + (∑ z : {c : OrderedFinpartition n // c.length ≠ 1}, W z.1) v := hsumEval
      _ = fderiv ℝ (b t) (F x) (orderedPartial n F x I) + Q v := by
        rw [hTopTerm]
  have hQweight :
      ‖Q‖ ≤ common *
        (2 * ((n + 1).factorial : ℝ) * flowHalfBinomialCoeff n) := by
    have hterm (z : {c : OrderedFinpartition n // c.length ≠ 1}) :
        ‖W z.1‖ ≤ common * flowPositivePartitionWeight z.1 := by
      have hlenPos : 0 < z.1.length :=
        z.1.length_pos (by omega)
      have hlen : 2 ≤ z.1.length := by
        have hne : z.1.length ≠ 1 := z.2
        omega
      simpa [W, H, G, y, F, common, Rflow] using Remainder.flowFaaTerm_bound hn hnN hb hXsmooth
        hCf hRf hB t x hDn z.1 hlen
    have hweightSplit := Fintype.sum_subtype_add_sum_subtype
      (fun c : OrderedFinpartition n => c.length = 1)
      (fun c => flowPositivePartitionWeight c)
    have hfirstWeightNonneg :
        0 ≤ ∑ z : {c : OrderedFinpartition n // c.length = 1},
          flowPositivePartitionWeight z.1 := by
      apply Finset.sum_nonneg
      intro z hz
      dsimp [flowPositivePartitionWeight]
      apply mul_nonneg (by positivity)
      apply Finset.prod_nonneg
      intro i hi
      exact mul_nonneg (by positivity)
        (flowHalfCoeff_nonneg_of_posSize
          (Nat.succ_le_iff.mpr (z.1.partSize_pos i)))
    have hcomplement :
        (∑ z : {c : OrderedFinpartition n // c.length ≠ 1},
          flowPositivePartitionWeight z.1) ≤
          ∑ c : OrderedFinpartition n, flowPositivePartitionWeight c := by
      linarith [hweightSplit]
    calc
      ‖Q‖ ≤ ∑ z : {c : OrderedFinpartition n // c.length ≠ 1}, ‖W z.1‖ :=
        norm_sum_le _ _
      _ ≤ ∑ z : {c : OrderedFinpartition n // c.length ≠ 1},
          common * flowPositivePartitionWeight z.1 :=
        Finset.sum_le_sum fun z hz => hterm z
      _ = common *
          ∑ z : {c : OrderedFinpartition n // c.length ≠ 1},
            flowPositivePartitionWeight z.1 := by rw [Finset.mul_sum]
      _ ≤ common *
          ∑ c : OrderedFinpartition n, flowPositivePartitionWeight c :=
        mul_le_mul_of_nonneg_left hcomplement (by positivity)
      _ = common *
          (2 * ((n + 1).factorial : ℝ) * flowHalfBinomialCoeff n) := by
        rw [orderedFinpartitionPositiveHalfBinomialResummation10421]
  have hdiff :
      orderedPartial n (fun z => b t (F z)) x I -
          fderiv ℝ (b t) (F x) (orderedPartial n F x I) = Q v := by
    rw [hdecomp]
    abel
  have hcoordNorm : ∏ j : Fin n, ‖v j‖ = 1 := by
    simp [v, coordinateVectorOne_norm]
  calc
    _ = ‖Q v‖ := by rw [hdiff]
    _ ≤ ‖Q‖ * ∏ j : Fin n, ‖v j‖ := Q.le_opNorm v
    _ = ‖Q‖ := by rw [hcoordNorm, mul_one]
    _ ≤ common * (2 * ((n + 1).factorial : ℝ) * flowHalfBinomialCoeff n) := hQweight
    _ = _ := by simp [common, Rflow]

end AVenhance.FaaDiBruno

end
