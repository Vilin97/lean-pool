/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.DualVC
import LeanPool.FormalLearningTheory.Complexity.Structures
import LeanPool.FormalLearningTheory.Complexity.Generalization
import LeanPool.FormalLearningTheory.Complexity.FiniteSupportUC
import LeanPool.FormalLearningTheory.PureMath.ApproxMinimax
import LeanPool.FormalLearningTheory.PureMath.FiniteVCApprox
import LeanPool.FormalLearningTheory.PureMath.BinaryMatrix

/-!
# Moran-Yehudayoff Compression Theorem

Finite VC dimension ↔ compression scheme with finite side information.

## Architecture

The forward direction (VCDim < ⊤ → compression) uses the Moran-Yehudayoff construction:
1. A proper finite-support learner (from VC + Sauer-Shelah + probabilistic method)
2. A hypothesis envelope (finite image of the learner on bounded subsamples)
3. An approximate minimax strategy on the agreement game
4. Sparse approximation via VC ε-approximation on agreement tests
5. Majority vote reconstruction with incidence side information

The reverse direction (compression → VCDim < ⊤) is by pigeonhole on
the bounded set of (kernel, info) pairs.

## No Measure Theory

The forward theorem is pure and combinatorial. It uses FinitePMF, Finset,
and finite games — no MeasureTheory.Measure, IsProbabilityMeasure, Measure.dirac,
or MeasurableSpace hypotheses.
-/

open Finset
noncomputable section
universe u

attribute [local instance] Classical.propDecidable

/-! ## Helper definitions -/

/-- Extract the domain points from a labeled sample. -/
def pointSupport {X : Type u} {m : ℕ} (S : Fin m → X × Bool) : Finset X :=
  Finset.univ.image (fun i => (S i).1)

/-- Build a labeled sample from a Finset of points and a concept. -/
def labeledSampleOfFinset {X : Type u} (c : X → Bool) (Z : Finset X) :
    Fin Z.card → X × Bool :=
  fun i => let x := (Z.equivFin.symm i : X); (x, c x)

/-- Weighted error of hypothesis h vs concept c over a FinitePMF on Y. -/
def supportError {X : Type u} (Y : Finset X) (q : FinitePMF ↥Y)
    (h : X → Bool) (c : X → Bool) : ℝ :=
  ∑ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (0 : ℝ) else 1)

/-- Weighted agreement = 1 - supportError. -/
lemma supportAgreement_eq_one_sub_supportError {X : Type u} (Y : Finset X)
    (q : FinitePMF ↥Y) (h c : X → Bool) :
    (∑ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (1 : ℝ) else 0)) =
    1 - supportError Y q h c := by
  simp only [supportError]
  linarith [show (∑ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (1 : ℝ) else 0)) +
      (∑ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (0 : ℝ) else 1)) = 1 from by
    rw [← Finset.sum_add_distrib]
    simp_rw [show ∀ y : ↥Y, q.prob y * (if h (y : X) = c (y : X) then (1 : ℝ) else 0) +
        q.prob y * (if h (y : X) = c (y : X) then (0 : ℝ) else 1) = q.prob y from
      fun y => by split_ifs <;> ring]
    exact q.prob_sum_one]

/-- supportError is nonneg. -/
lemma supportError_nonneg {X : Type u} (Y : Finset X) (q : FinitePMF ↥Y)
    (h c : X → Bool) : 0 ≤ supportError Y q h c :=
  Finset.sum_nonneg fun y _ =>
    mul_nonneg (q.prob_nonneg y) (by split_ifs <;> norm_num)

/-- supportError is at most 1. -/
lemma supportError_le_one {X : Type u} (Y : Finset X) (q : FinitePMF ↥Y)
    (h c : X → Bool) : supportError Y q h c ≤ 1 := by
  calc supportError Y q h c
      ≤ ∑ y : ↥Y, q.prob y := Finset.sum_le_sum fun y _ =>
        mul_le_of_le_one_right (q.prob_nonneg y) (by split_ifs <;> norm_num)
    _ = 1 := q.prob_sum_one

/-! ## Structure: Proper Finite-Support Learner -/

/-- A proper finite-support learner for a concept class C.
    This structure captures the existence of a bounded-support ERM
    with error at most 1 / 3 for any C-realizable finite distribution.
    CORRECTED: good_on_support returns Finset X (not Fin k → X). -/
structure ProperFiniteSupportLearner (X : Type u) (C : ConceptClass X Bool) where
  /-- Uniform upper bound on the selected support size. -/
  sampleBound : ℕ
  /-- Learner evaluated on a finite labeled sample. -/
  learn : {m : ℕ} → (Fin m → X × Bool) → (X → Bool)
  output_mem : ∀ {m : ℕ} (S : Fin m → X × Bool), learn S ∈ C
  good_on_support : ∀ (c : X → Bool) (_ : c ∈ C) (Y : Finset X)
    (q : FinitePMF ↥Y),
    ∃ Z : Finset X, Z ⊆ Y ∧ Z.card ≤ sampleBound ∧
      supportError Y q (learn (labeledSampleOfFinset c Z)) c ≤ 1 / 3

/-- The disagreement family: for each h ∈ C, the test y ↦ decide(h(y) ≠ c(y))
    restricted to Y. Used for the VC approximation step in the proper learner proof. -/
private def disagreementFamily
    {X : Type u} (C : ConceptClass X Bool)
    (c : X → Bool) (Y : Finset X) : Finset (↥Y → Bool) :=
  Finset.univ.image (fun (h : ↥Y → Bool) => h) |>.filter (fun a =>
    ∃ h ∈ C, ∀ y : ↥Y, a y = decide (h (y : X) ≠ c (y : X)))

/-- VC dimension of the disagreement family is bounded by VCDim(C).
    Restriction to Y and xor with c do not increase shattering dimension. -/
private lemma disagreementFamily_boolVCDim_le
    {X : Type u} [DecidableEq X]
    (C : ConceptClass X Bool) (c : X → Bool) (Y : Finset X) {d : ℕ}
    (hvc : VCDim X C ≤ ↑d) :
    (disagreementFamily C c Y).boolVCDim ≤ d := by
  simp only [Finset.boolVCDim, Finset.vcDim]
  apply Finset.sup_le
  intro T hT
  have hTs := Finset.mem_shatterer.mp hT
  let S := T.map ⟨Subtype.val, Subtype.val_injective⟩
  have mem_S : ∀ y : ↥Y, y ∈ T → (y : X) ∈ S := fun y hy => Finset.mem_map.mpr ⟨y, hy, rfl⟩
  suffices hS_shatt : Shatters X C S by
    exact WithTop.coe_le_coe.mp (le_trans
      (Finset.card_map _ ▸ le_iSup₂_of_le S hS_shatt le_rfl) hvc)
  intro g
  let pred : ↥Y → Bool := fun y =>
    if hy : y ∈ T then decide (g ⟨y.val, mem_S y hy⟩ ≠ c y.val) else false
  let t := T.filter (fun y => pred y = true)
  have ht_sub : t ⊆ T := Finset.filter_subset (fun y => pred y = true) T
  obtain ⟨u, hu, hTu⟩ := hTs ht_sub
  simp only [boolFamilyToFinsetFamily, Finset.mem_image] at hu
  obtain ⟨a, ha, rfl⟩ := hu
  simp only [disagreementFamily, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and] at ha
  obtain ⟨_, h_concept, hcC, ha_eq⟩ := ha
  refine ⟨h_concept, hcC, fun ⟨x, hxS⟩ => ?_⟩
  obtain ⟨y, hyT, hyx⟩ := Finset.mem_map.mp hxS
  subst hyx
  have h_mem_iff : y ∈ Finset.univ.filter (fun z => a z = true) ↔ y ∈ t := by
    constructor
    · intro hf; exact hTu ▸ Finset.mem_inter.mpr ⟨hyT, hf⟩
    · intro ht'; exact (Finset.mem_inter.mp (hTu ▸ ht')).2
  have h_ay_iff : a y = true ↔ g ⟨y.val, hxS⟩ ≠ c y.val := by
    rw [show (a y = true) ↔ y ∈ Finset.univ.filter (fun z => a z = true) from
      by simp [Finset.mem_filter], h_mem_iff]
    simp only [t, pred, Finset.mem_filter, hyT, dite_true, decide_eq_true_eq]
    tauto
  have ha_y := ha_eq y
  change h_concept (y : X) = g ⟨(y : X), hxS⟩
  by_cases heq : h_concept (y : X) = c (y : X)
  · have hgeq : g ⟨y.val, hxS⟩ = c y.val := by
      by_contra h
      exact absurd (h_ay_iff.mpr h) (by rw [show a y = false from by rw [ha_y]; simp [heq]]; simp)
    rw [heq, hgeq]
  · have hgne := h_ay_iff.mp (show a y = true from by rw [ha_y]; simp [heq])
    cases hc : c (y : X) <;> cases hh : h_concept (y : X) <;>
      cases hg : g ⟨y.val, hxS⟩ <;> simp_all

/-- supportError expressed in terms of boolTestExpectation of a disagreement test. -/
private lemma supportError_eq_boolTestExpectation
    {X : Type u} (Y : Finset X) (q : FinitePMF ↥Y)
    (h c : X → Bool) :
    supportError Y q h c =
    boolTestExpectation q (fun y : ↥Y => decide (h (y : X) ≠ c (y : X))) := by
  simp only [supportError, boolTestExpectation, trueExpectation]
  congr 1; ext y
  by_cases heq : h (y : X) = c (y : X) <;> simp [heq]

/-- Finite VC dimension implies existence of a proper finite-support learner.
    The construction uses ERM + finite_support_vc_approx on the disagreement family. -/
theorem vcdim_finite_imp_proper_finite_support_learner
    (X : Type u) (C : ConceptClass X Bool)
    (hCne : C.Nonempty) (hC : VCDim X C < ⊤) :
    ∃ _L : ProperFiniteSupportLearner X C, True := by
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hC)
  obtain ⟨c₀, hc₀⟩ := hCne
  let learn : {m : ℕ} → (Fin m → X × Bool) → (X → Bool) := fun {m} S =>
    if h : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2 then h.choose else c₀
  have learn_mem : ∀ {m : ℕ} (S : Fin m → X × Bool), learn S ∈ C := by
    intro m S; simp only [learn]
    split
    · next h => exact h.choose_spec.1
    · exact hc₀
  have learn_consistent : ∀ {m : ℕ} (S : Fin m → X × Bool),
      (∃ c ∈ C, ∀ i, c (S i).1 = (S i).2) → ∀ i, learn S (S i).1 = (S i).2 := by
    intro m S hreal i; simp only [learn, dif_pos hreal]; exact hreal.choose_spec.2 i
  obtain ⟨T, hTpos, hApprox⟩ := finite_support_vc_approx d (1 / 3) (by norm_num)
  exact ⟨⟨T, learn, @learn_mem, fun c hc Y q => by
    classical
    haveI : DecidableEq X := Classical.decEq X
    let A := disagreementFamily C c Y
    have hA : A.boolVCDim ≤ d := disagreementFamily_boolVCDim_le C c Y (le_of_eq hd.symm)
    obtain ⟨hs, hhs⟩ := hApprox A hA q
    let Z : Finset X := Finset.univ.image (fun t => ((hs t : ↥Y) : X))
    refine ⟨Z, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Z, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨t, rfl⟩ := hx; exact (hs t).property
    · calc Z.card ≤ Finset.univ.card := Finset.card_image_le
        _ = T := Fintype.card_fin T
    · let h_out := learn (labeledSampleOfFinset c Z)
      let disagree : ↥Y → Bool := fun y => decide (h_out (y : X) ≠ c (y : X))
      have disagree_mem : disagree ∈ A := by
        simp only [A, disagreementFamily, Finset.mem_filter, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact ⟨⟨disagree, rfl⟩, h_out, learn_mem _, fun y => rfl⟩
      rw [supportError_eq_boolTestExpectation]
      have hclose := hhs disagree disagree_mem
      have h_emp_zero : boolTestExpectation (empiricalPMF hTpos hs) disagree = 0 := by
        rw [boolTestExpectation_empirical_eq_avg hTpos hs disagree, div_eq_zero_iff]
        left; apply Finset.sum_eq_zero; intro t _
        have hreal_Z : ∃ c' ∈ C, ∀ i : Fin Z.card,
            c' ((labeledSampleOfFinset c Z) i).1 = ((labeledSampleOfFinset c Z) i).2 :=
          ⟨c, hc, fun i => by simp [labeledSampleOfFinset]⟩
        have ht_in_Z : ((hs t : ↥Y) : X) ∈ Z := by
          simp only [Z, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨t, rfl⟩
        set i_Z := Z.equivFin ⟨((hs t : ↥Y) : X), ht_in_Z⟩
        have hcons_i := learn_consistent (labeledSampleOfFinset c Z) hreal_Z i_Z
        simp only [labeledSampleOfFinset] at hcons_i
        rw [Z.equivFin.symm_apply_apply] at hcons_i
        have hdisagree_false : disagree (hs t) = false := by
          simp only [disagree, h_out, decide_eq_false_iff_not, ne_eq, not_not]
          exact hcons_i
        rw [hdisagree_false]; simp
      rw [h_emp_zero, sub_zero] at hclose
      exact le_trans (le_abs_self _) hclose
    ⟩, trivial⟩

/-! ## Hypothesis Envelope -/

/-- Bounded subsamples: all subsets of Y with cardinality ≤ s. -/
def boundedSubsamples {X : Type u} (Y : Finset X) (s : ℕ) : Finset (Finset X) :=
  Y.powerset.filter (fun Z => Z.card ≤ s)

/-- The hypothesis envelope: the finite set of all possible learner outputs
    on bounded subsamples of Y, labeled by concept c. -/
def hypothesisEnvelope {X : Type u} {C : ConceptClass X Bool}
    (L : ProperFiniteSupportLearner X C) (c : X → Bool) (Y : Finset X) :
    Finset (X → Bool) :=
  (boundedSubsamples Y L.sampleBound).image (fun Z =>
    L.learn (labeledSampleOfFinset c Z))

/-- Every hypothesis in the envelope is in C. -/
lemma hypothesisEnvelope_sub {X : Type u} {C : ConceptClass X Bool}
    (L : ProperFiniteSupportLearner X C) (c : X → Bool) (Y : Finset X)
    (h : X → Bool) (hh : h ∈ hypothesisEnvelope L c Y) : h ∈ C := by
  simp only [hypothesisEnvelope, Finset.mem_image] at hh
  obtain ⟨Z, _, rfl⟩ := hh
  exact L.output_mem _

/-! ## Agreement Tests -/

/-- Per-point agreement test: for a fixed point x ∈ Y and concept c,
    maps hypothesis h to whether h(x) = c(x). -/
def agreeTest {X : Type u} (c : X → Bool) (x : X)
    (HY : Finset (X → Bool)) : ↥HY → Bool :=
  fun h => decide (h.val x = c x)

/-- The family of agreement tests over all points in Y. -/
def agreeTests {X : Type u} (c : X → Bool) (Y : Finset X)
    (HY : Finset (X → Bool)) : Finset (↥HY → Bool) :=
  Y.image (fun x => agreeTest c x HY)

private theorem boolTestExpectation_empirical_agreeTest_eq_avg {X : Type u} {T : ℕ}
    {HY : Finset (X → Bool)} [Fintype ↥HY] [DecidableEq ↥HY]
    (hT : 0 < T) (reps : Fin T → ↥HY) (c : X → Bool) (x : X) :
    boolTestExpectation (empiricalPMF hT reps) (agreeTest c x HY) =
      (∑ t : Fin T, if (reps t).val x = c x then (1 : ℝ) else 0) / T := by
  rw [boolTestExpectation_empirical_eq_avg]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : (↑(reps t) : X → Bool) x = c x
  · simp [agreeTest, h]
  · simp [agreeTest, h]

/-! ## Roundtrip helpers for the compression proof -/

/-- Encode a witness set `W` as the set of kernel positions of the pairs `(x, c x)`.
The bound `kernel.card ≤ K` is fed into the encoding through the `if` branch, so the
result has the same shape as the current `compressCore` code. -/
def encodeWitnessInfo
    {X : Type u} [DecidableEq X]
    (kernel : Finset (X × Bool)) (c : X → Bool) (K : ℕ)
    (W : Finset X) : Finset (Fin K) :=
  W.attach.biUnion (fun x =>
    if hmk : ((x : X), c x) ∈ kernel then
      if hlt : (kernel.equivFin ⟨((x : X), c x), hmk⟩).val < K then
        {⟨(kernel.equivFin ⟨((x : X), c x), hmk⟩).val, hlt⟩}
      else ∅
    else ∅)

/-- Decode the X-coordinates of a block from kernel positions. This matches the
current `blockHyp` shape. -/
def decodeWitnessXCoords
    {X : Type u} (Z : Finset (X × Bool)) {K : ℕ} (idxs : Finset (Fin K)) : Finset X :=
  idxs.biUnion (fun idx =>
    if h : (idx : ℕ) < Z.card then
      {((Z.equivFin.symm ⟨(idx : ℕ), h⟩ : Z) : X × Bool).1}
    else ∅)

/-- Decode labels from the kernel. This is exactly the current MY reconstruction
convention in your file. -/
def decodeWitnessLabel {X : Type u} [DecidableEq X] (Z : Finset (X × Bool)) : X → Bool :=
  fun x => decide ((x, true) ∈ Z)

/-- If every `(x, c x)` with `x ∈ W` lies in `kernel`, and `kernel.card ≤ K`, then
decoding the encoded witness positions gives back exactly `W`. -/
lemma decodeWitnessXCoords_encode_eq
    {X : Type u} [DecidableEq X]
    (kernel : Finset (X × Bool)) (c : X → Bool) {K : ℕ}
    (W : Finset X)
    (hK : kernel.card ≤ K)
    (hWker : ∀ x ∈ W, (x, c x) ∈ kernel) :
    decodeWitnessXCoords kernel (encodeWitnessInfo kernel c K W) = W := by
  ext x
  constructor
  · intro hx
    unfold decodeWitnessXCoords at hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨idx, hidx_mem, hx⟩ := hx
    unfold encodeWitnessInfo at hidx_mem
    simp only [Finset.mem_biUnion] at hidx_mem
    obtain ⟨⟨x0, hx0W⟩, _, hidx_mem2⟩ := hidx_mem
    by_cases hmk : ((x0 : X), c x0) ∈ kernel
    · by_cases hlt : (kernel.equivFin ⟨(x0, c x0), hmk⟩).val < K
      · simp only [dif_pos hmk, dif_pos hlt, Finset.mem_singleton] at hidx_mem2
        subst hidx_mem2
        simp only [dif_pos (kernel.equivFin ⟨(x0, c x0), hmk⟩).isLt, Finset.mem_singleton] at hx
        rw [congrArg Subtype.val (Equiv.symm_apply_apply (kernel.equivFin) ⟨(x0, c x0), hmk⟩)]
          at hx
        exact (by simpa using hx : x = x0) ▸ hx0W
      · simp only [dif_pos hmk, dif_neg hlt] at hidx_mem2; exact absurd hidx_mem2 (by simp)
    · simp only [dif_neg hmk] at hidx_mem2; exact absurd hidx_mem2 (by simp)
  · intro hxW
    have hmk : (x, c x) ∈ kernel := hWker x hxW
    have hltK : (kernel.equivFin ⟨(x, c x), hmk⟩).val < K :=
      lt_of_lt_of_le (kernel.equivFin ⟨(x, c x), hmk⟩).isLt hK
    have hidx_in_enc : ⟨(kernel.equivFin ⟨(x, c x), hmk⟩).val, hltK⟩ ∈
        encodeWitnessInfo kernel c K W := by
      simp only [encodeWitnessInfo, Finset.mem_biUnion, Finset.mem_attach, true_and]
      exact ⟨⟨x, hxW⟩, by simp [hmk, hltK]⟩
    change x ∈ decodeWitnessXCoords kernel (encodeWitnessInfo kernel c K W)
    simp only [decodeWitnessXCoords, Finset.mem_biUnion]
    exact ⟨⟨(kernel.equivFin ⟨(x, c x), hmk⟩).val, hltK⟩, hidx_in_enc, by
      simp [(kernel.equivFin ⟨(x, c x), hmk⟩).isLt, Equiv.symm_apply_apply]⟩

/-- On the encoded witness support, the decoded label function agrees with the true
label function `c`, provided every pair in the kernel has the correct second coordinate. -/
lemma decodeWitnessLabel_eq_on_encoded
    {X : Type u} [DecidableEq X]
    (kernel : Finset (X × Bool)) (c : X → Bool) (W : Finset X)
    (hWker : ∀ x ∈ W, (x, c x) ∈ kernel)
    (hlabels : ∀ p ∈ kernel, p.2 = c p.1) :
    ∀ x ∈ W, decodeWitnessLabel kernel x = c x := by
  intro x hxW
  unfold decodeWitnessLabel
  by_cases hc : c x = true
  · have hmem : (x, true) ∈ kernel := by
      simpa [hc] using hWker x hxW
    simp [hmem, hc]
  · have hnot : (x, true) ∉ kernel := by
      intro htrue
      have hcoord : true = c x := by
        simpa using hlabels (x, true) htrue
      exact hc hcoord.symm
    have hfalse : c x = false := by
      cases hcx : c x <;> simp_all
    simp [hnot, hfalse]

/-- If two label functions agree on all points of `Z`, then the labeled samples they
induce on `Z.equivFin` are equal. -/
lemma labeledSampleOfFinset_eq_of_eq_on_support
    {X : Type u}
    {ℓ₁ ℓ₂ : X → Bool} {Z : Finset X}
    (hℓ : ∀ x ∈ Z, ℓ₁ x = ℓ₂ x) :
    labeledSampleOfFinset ℓ₁ Z = labeledSampleOfFinset ℓ₂ Z := by
  funext j
  simp only [labeledSampleOfFinset]
  congr 1
  exact hℓ _ (Z.equivFin.symm j).property

/-- Generic roundtrip theorem for the compression reconstruction invariant.

If:
* `encodeWitnessInfo` is used in `compressCore`,
* `decodeWitnessXCoords` and `decodeWitnessLabel` are used in `blockHyp`, and
* the kernel contains the witness pairs with the correct labels,

then the decoded block hypothesis is exactly the representative hypothesis. -/
theorem roundtrip_blockHyp_eq_rep
    {X : Type u} [DecidableEq X]
    (learn : {m : ℕ} → (Fin m → X × Bool) → (X → Bool))
    (kernel : Finset (X × Bool)) (c : X → Bool) (K : ℕ)
    (W : Finset X) (h : X → Bool)
    (hK : kernel.card ≤ K)
    (hWker : ∀ x ∈ W, (x, c x) ∈ kernel)
    (hlabels : ∀ p ∈ kernel, p.2 = c p.1)
    (hrep : learn (labeledSampleOfFinset c W) = h)
    (x : X) :
    let info : Finset (Fin K) := encodeWitnessInfo kernel c K W
    let blockXCoords : Finset X := decodeWitnessXCoords kernel info
    let blockLabel : X → Bool := decodeWitnessLabel kernel
    learn (labeledSampleOfFinset blockLabel blockXCoords) x = h x := by
  dsimp
  rw [decodeWitnessXCoords_encode_eq kernel c W hK hWker,
    labeledSampleOfFinset_eq_of_eq_on_support
      (decodeWitnessLabel_eq_on_encoded kernel c W hWker hlabels),
    hrep]

/-- VC dimension of the agreement-test family is bounded by `2^(d+1) - 1`,
    where `d` bounds the VC dimension of the concept class `C`.
    Uses Assouad's coding argument directly: if a shattered set `T` in `↥HY` has
    `|T| ≥ 2^(d+1)`, embed bitstrings into `T`, extract `d+1` distinct points from `Y`
    via shattering, and show these points are shattered by `C` (using the XOR trick
    where `b(j) = decide(g(x_j) = c(x_j))` absorbs the agree/disagree flip). -/
private lemma agreeTests_boolVCDim_le
    {X : Type u}
    (C : ConceptClass X Bool) (c : X → Bool) (Y : Finset X)
    (HY : Finset (X → Bool)) (hHY : ∀ h ∈ HY, h ∈ C)
    {d : ℕ} (hvc : VCDim X C ≤ ↑d) :
    (agreeTests c Y HY).boolVCDim ≤ 2 ^ (d + 1) - 1 := by
  classical
  simp only [Finset.boolVCDim, Finset.vcDim]
  apply Finset.sup_le
  intro T hT
  have hTs := Finset.mem_shatterer.mp hT
  by_contra hlt
  push Not at hlt
  have hge : 2 ^ (d + 1) ≤ T.card := by omega
  let eT := T.equivFin
  let eFun : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq (by simp [Fintype.card_bool, Fintype.card_fin])
  let eFin : Fin (2 ^ (d + 1)) ↪ Fin T.card := Fin.castLEEmb hge
  let eFinT : Fin T.card ≃ ↥T := eT.symm
  let embed : (Fin (d + 1) → Bool) → ↥T := eFinT ∘ eFin ∘ eFun
  have hembed_inj : Function.Injective embed := by
    intro a b hab; simp only [embed, Function.comp] at hab
    exact eFun.injective (eFin.injective (eFinT.injective hab))
  let halfSet' (j : Fin (d + 1)) : Finset ↥HY :=
    (Finset.univ.filter (fun b : Fin (d + 1) → Bool => b j = true)).image
      (fun b => (embed b).val)
  have halfSet'_sub : ∀ j, halfSet' j ⊆ T := by
    intro j h hh
    simp only [halfSet', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    obtain ⟨b, _, rfl⟩ := hh
    exact (embed b).property
  have hpoints : ∀ j : Fin (d + 1), ∃ x ∈ Y,
      ∀ h : ↥HY, h ∈ T → ((h.val x = c x) ↔ h ∈ halfSet' j) := by
    intro j
    obtain ⟨u, hu, hTu⟩ := hTs (halfSet'_sub j)
    simp only [boolFamilyToFinsetFamily, Finset.mem_image] at hu
    obtain ⟨f, hf, rfl⟩ := hu
    simp only [agreeTests, Finset.mem_image] at hf
    obtain ⟨x, hxY, rfl⟩ := hf
    refine ⟨x, hxY, fun h hmem => ?_⟩
    constructor
    · intro hagree
      exact hTu ▸ Finset.mem_inter.mpr
        ⟨hmem, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [agreeTest, hagree]⟩⟩
    · intro h_in_half
      have := Finset.mem_inter.mp (hTu ▸ h_in_half)
      simp only [Finset.mem_filter, agreeTest, decide_eq_true_eq] at this
      exact this.2.2
  choose x hxY hx using hpoints
  have hx_inj : Function.Injective x := by
    intro j k hjk; by_contra hjk_ne
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    let h0 : ↥T := embed b0
    have h0_in_j : h0.val ∈ halfSet' j := by
      simp only [halfSet', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨b0, by simp [b0], rfl⟩
    have h0_nin_k : h0.val ∉ halfSet' k := by
      simp only [halfSet', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ⟨b', hb'k, hb'eq⟩
      have := hembed_inj (Subtype.ext hb'eq : embed b' = h0)
      rw [this] at hb'k; simp [b0] at hb'k; exact hjk_ne hb'k.symm
    exact h0_nin_k ((hx k h0.val h0.property).mp (hjk ▸ (hx j h0.val h0.property).mpr h0_in_j))
  let P : Finset X := Finset.univ.image x
  have hP_card : P.card = d + 1 := by
    simp only [P, Finset.card_image_of_injective _ hx_inj, Finset.card_univ, Fintype.card_fin]
  have hP_shatters : Shatters X C P := by
    intro g
    have hx_mem : ∀ j, x j ∈ P := fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    let b : Fin (d + 1) → Bool := fun j => decide (g ⟨x j, hx_mem j⟩ = c (x j))
    let h_wit : ↥T := embed b
    refine ⟨h_wit.val.val, hHY _ h_wit.val.property, fun ⟨y, hy⟩ => ?_⟩
    rw [Finset.mem_image] at hy; obtain ⟨j, _, rfl⟩ := hy
    have h_wit_in_half_iff : h_wit.val ∈ halfSet' j ↔ b j = true := by
      simp only [halfSet', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨b', hb'j, hb'eq⟩ => by
          rwa [← hembed_inj (Subtype.ext hb'eq : embed b' = h_wit)],
        fun hbj => ⟨b, hbj, rfl⟩⟩
    have h_agree_iff := (hx j h_wit.val h_wit.property).trans h_wit_in_half_iff
    change h_wit.val.val (x j) = g ⟨x j, hx_mem j⟩
    by_cases heq : g ⟨x j, hx_mem j⟩ = c (x j)
    · rw [heq]; exact h_agree_iff.mpr (by simp [b, heq])
    · have hbj : b j = false := by simp only [b, decide_eq_false_iff_not]; exact heq
      have h_ne : h_wit.val.val (x j) ≠ c (x j) :=
        fun hc => Bool.noConfusion (show true = false from hbj ▸ (h_agree_iff.mp hc).symm)
      cases hc : c (x j) <;> cases hw : h_wit.val.val (x j) <;>
        cases hg : g ⟨x j, hx_mem j⟩ <;> simp_all
  have h_vc_ge : (P.card : WithTop ℕ) ≤ VCDim X C := le_iSup₂_of_le P hP_shatters le_rfl
  rw [hP_card] at h_vc_ge
  exact absurd (le_trans h_vc_ge hvc) (by push Not; exact_mod_cast Nat.lt_succ_of_le le_rfl)

/-! ## Moran-Yehudayoff forward construction — universe-fixed closure helpers -/

/-- Fix the hidden `Info` universe parameter of `CompressionSchemeWithInfo` to `0`.
    This resolves the universe elaboration obstruction: `Fin T → Finset (Fin K)` is
    `Type 0`, while `CompressionSchemeWithInfo X Bool C` with `X : Type u` infers
    `Info : Type u`. Pinning to `.{u, 0, 0}` allows `Type 0` Info directly. -/
abbrev CompressionSchemeWithInfo0 (X : Type u) (Y : Type) (C : ConceptClass X Y) :=
  CompressionSchemeWithInfo.{u, 0, 0} X Y C

/-- Concrete side information for the MY construction: each of the `T` recovered
    blocks is represented by the set of kernel positions it uses. -/
abbrev IncidenceInfo (T K : ℕ) : Type := Fin T → Finset (Fin K)

instance instFintypeIncidenceInfo (T K : ℕ) : Fintype (IncidenceInfo T K) := inferInstance

/-- Plain wrapper: build a `CompressionSchemeWithInfo0` from incidence-coded components. -/
private def mkIncidenceScheme
    {X : Type u} {C : ConceptClass X Bool}
    (T K : ℕ)
    (compressCore : {m : ℕ} → (Fin m → X × Bool) → Finset (X × Bool) × IncidenceInfo T K)
    (reconstructCore : Finset (X × Bool) → IncidenceInfo T K → (X → Bool))
    (hsmall : ∀ {m : ℕ} (S : Fin m → X × Bool), (compressCore S).1.card ≤ K)
    (hsub : ∀ {m : ℕ} (S : Fin m → X × Bool), ↑(compressCore S).1 ⊆ Set.range S)
    (hcorrect : ∀ {m : ℕ} (S : Fin m → X × Bool),
      (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) →
      ∀ i : Fin m,
        reconstructCore (compressCore S).1 (compressCore S).2 (S i).1 = (S i).2) :
    CompressionSchemeWithInfo0 X Bool C := by
  classical
  let InfoTy : Type := IncidenceInfo T K
  exact {
    Info := InfoTy
    info_finite := inferInstance
    compress := fun {m} S => compressCore S
    reconstruct := reconstructCore
    kernelSize := K
    compress_small := hsmall
    compress_sub := hsub
    correct := hcorrect
  }

/-- The sum of Boolean indicators equals the cardinality of the agreeing filter. -/
private lemma sum_indicator_eq_card_filter
    {T : ℕ} (votes : Fin T → Bool) (y : Bool) :
    (∑ t : Fin T, if votes t = y then (1 : ℝ) else 0)
      = (Finset.univ.filter (fun t => votes t = y)).card := by
  simp

/-- Majority vote returns the target label if strictly more than half agree. -/
private lemma majority_vote_eq_of_agree_gt_half
    {T : ℕ} (hT : 0 < T) (votes : Fin T → Bool) (y : Bool)
    (hmajor : ((∑ t : Fin T, if votes t = y then (1 : ℝ) else 0) / T) > (1 / 2 : ℝ)) :
    majority_vote T votes = y := by
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  by_cases hy : y
  · subst hy
    have hgt_nat : 2 * (Finset.univ.filter (fun t => votes t = true)).card > T := by
      exact_mod_cast show (2 * (Finset.univ.filter (fun t => votes t = true)).card : ℝ) > T by
        rw [sum_indicator_eq_card_filter votes true] at hmajor
        rw [gt_iff_lt, lt_div_iff₀ hTreal] at hmajor; linarith
    simp [majority_vote, hgt_nat]
  · have hyf : y = false := by cases y <;> simp_all
    subst hyf
    have hgt_false_nat : 2 * (Finset.univ.filter (fun t => votes t = false)).card > T := by
      exact_mod_cast show (2 * (Finset.univ.filter (fun t => votes t = false)).card : ℝ) > T by
        rw [sum_indicator_eq_card_filter votes false] at hmajor
        rw [gt_iff_lt, lt_div_iff₀ hTreal] at hmajor; linarith
    simp [majority_vote, show ¬2 * (Finset.univ.filter (fun t => votes t = true)).card > T from by
      have : (Finset.univ.filter (fun t => votes t = true)).card +
             (Finset.univ.filter (fun t => votes t = false)).card = T := by
        simpa [Bool.eq_false_eq_not_eq_true, Finset.card_univ] using
          Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin T)))
            (p := fun t => votes t = true)
      omega]

/-- The actual final closure helper. Packages the majority-vote construction.
    If decoded hypotheses agree with reference hypotheses on sample points,
    and majority of reference hypotheses agree with each label,
    then majority-vote reconstruction is correct. -/
private def mkIncidenceSchemeOfMajority
    {X : Type u} {C : ConceptClass X Bool}
    (T K : ℕ)
    (compressCore : {m : ℕ} → (Fin m → X × Bool) → Finset (X × Bool) × IncidenceInfo T K)
    (blockHyp : Finset (X × Bool) → IncidenceInfo T K → Fin T → X → Bool)
    (rowHyp : {m : ℕ} → (S : Fin m → X × Bool) →
      (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) → Fin T → X → Bool)
    (hT : 0 < T)
    (hsmall : ∀ {m : ℕ} (S : Fin m → X × Bool), (compressCore S).1.card ≤ K)
    (hsub : ∀ {m : ℕ} (S : Fin m → X × Bool), ↑(compressCore S).1 ⊆ Set.range S)
    (hagree : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m) (t : Fin T),
      blockHyp (compressCore S).1 (compressCore S).2 t (S i).1 = rowHyp S hreal t (S i).1)
    (hmajor : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m),
      ((∑ t : Fin T,
          if rowHyp S hreal t (S i).1 = (S i).2 then (1 : ℝ) else 0) / T) > (1 / 2 : ℝ)) :
    CompressionSchemeWithInfo0 X Bool C := by
  classical
  refine mkIncidenceScheme (X := X) (C := C) T K
    compressCore
    (fun Z info x => majority_vote T (fun t => blockHyp Z info t x))
    hsmall hsub ?_
  intro m S hreal i
  exact (by congr 1; funext t; exact hagree S hreal i t :
      majority_vote T (fun t => blockHyp (compressCore S).1 (compressCore S).2 t (S i).1)
        = majority_vote T (fun t => rowHyp S hreal t (S i).1)).trans
    (majority_vote_eq_of_agree_gt_half hT _ (S i).2 (hmajor S hreal i))

/-- Final existential wrapper: closes the theorem in the exact form expected. -/
private theorem finalizeIncidenceScheme
    {X : Type u} {C : ConceptClass X Bool}
    (T K : ℕ)
    (compressCore : {m : ℕ} → (Fin m → X × Bool) → Finset (X × Bool) × IncidenceInfo T K)
    (blockHyp : Finset (X × Bool) → IncidenceInfo T K → Fin T → X → Bool)
    (rowHyp : {m : ℕ} → (S : Fin m → X × Bool) →
      (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) → Fin T → X → Bool)
    (hT : 0 < T)
    (hsmall : ∀ {m : ℕ} (S : Fin m → X × Bool), (compressCore S).1.card ≤ K)
    (hsub : ∀ {m : ℕ} (S : Fin m → X × Bool), ↑(compressCore S).1 ⊆ Set.range S)
    (hagree : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m) (t : Fin T),
      blockHyp (compressCore S).1 (compressCore S).2 t (S i).1 = rowHyp S hreal t (S i).1)
    (hmajor : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m),
      ((∑ t : Fin T,
          if rowHyp S hreal t (S i).1 = (S i).2 then (1 : ℝ) else 0) / T) > (1 / 2 : ℝ)) :
    ∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k := by
  exact ⟨_, mkIncidenceSchemeOfMajority
      (X := X) (C := C)
      T K compressCore blockHyp rowHyp hT hsmall hsub hagree hmajor, rfl⟩

/-- For each C-realizable sample, the proper learner provides a row-response
    for the minimax game on the hypothesis envelope. -/
private lemma good_on_support_gives_row_response
    {X : Type u} {C : ConceptClass X Bool}
    (L : ProperFiniteSupportLearner X C)
    (c : X → Bool) (hc : c ∈ C) (Y : Finset X) [Nonempty ↥Y]
    (HY : Finset (X → Bool))
    (hHY : HY = hypothesisEnvelope L c Y) :
    ∀ q : FinitePMF ↥Y, ∃ h : ↥HY,
      (2 : ℝ) / 3 ≤ ∑ y : ↥Y, q.prob y *
        (if decide (h.val (y : X) = c (y : X)) then (1 : ℝ) else 0) := by
  intro q
  obtain ⟨Z, hZY, hZcard, hZerr⟩ := L.good_on_support c hc Y q
  let h := L.learn (labeledSampleOfFinset c Z)
  refine ⟨⟨h, by rw [hHY]; exact Finset.mem_image.mpr ⟨Z, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hZY, hZcard⟩, rfl⟩⟩, ?_⟩
  have hag := supportAgreement_eq_one_sub_supportError Y q h c
  simp_rw [decide_eq_true_eq] at *; linarith

@[reducible]
private def pointSupportNonempty {X : Type u} {m : ℕ} (S : Fin m → X × Bool)
    (hm : 0 < m) : Nonempty ↥(pointSupport S) :=
  ⟨⟨(S ⟨0, hm⟩).1, by simp [pointSupport, Finset.mem_image]⟩⟩

private def moranBlockHyp {X : Type u} {C : ConceptClass X Bool} [DecidableEq X]
    (L : ProperFiniteSupportLearner X C) {T K : ℕ}
    (Z : Finset (X × Bool)) (info : IncidenceInfo T K) (t : Fin T) (x : X) : Bool :=
  L.learn
    (labeledSampleOfFinset (decodeWitnessLabel Z) (decodeWitnessXCoords Z (info t))) x

private theorem moranKernel_labels {X : Type u} [DecidableEq X] {T : ℕ} (c : X → Bool)
    (getWitness : Fin T → Finset X) :
    ∀ pair ∈ Finset.univ.biUnion (fun t => (getWitness t).image (fun x => (x, c x))),
      pair.2 = c pair.1 := by
  intro pair hp
  simp only [Finset.mem_biUnion, Finset.mem_image] at hp
  obtain ⟨_, _, x, _, rfl⟩ := hp
  rfl

private theorem witness_mem_moranKernel {X : Type u} [DecidableEq X] {T : ℕ} (c : X → Bool)
    (getWitness : Fin T → Finset X) (t : Fin T) {x : X} (hx : x ∈ getWitness t) :
    (x, c x) ∈ Finset.univ.biUnion (fun t => (getWitness t).image (fun x => (x, c x))) := by
  exact Finset.mem_biUnion.mpr ⟨t, by simp, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

/-- The Moran-Yehudayoff forward construction. Uses `finalizeIncidenceScheme`
    to package the majority-vote scheme with universe-correct Info type.

    The agent must provide: `compressCore`, `blockHyp`, `rowHyp`,
    `hsmall`, `hsub`, `hagree`, `hmajor`. These are the MY wiring. -/
private theorem moran_yehudayoff_forward_construction
    (X : Type u) (C : ConceptClass X Bool)
    (_hne : C.Nonempty)
    (L : ProperFiniteSupportLearner X C)
    (hC : VCDim X C < ⊤)
    (_K : ℕ) :
    ∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k := by
  classical
  haveI : DecidableEq X := Classical.decEq X
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hC)
  let s := L.sampleBound
  obtain ⟨Tvc, hTvcPos, hVCApprox⟩ :=
    finite_support_vc_approx (2 ^ (d + 1) - 1) (1 / 24) (by norm_num)
  let Kreal := Tvc * s
  let mkReps : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) (hm : 0 < m),
      Fin Tvc → ↥(hypothesisEnvelope L hreal.choose (pointSupport S)) := fun {m} S hreal hm =>
      let c := hreal.choose; let Y := pointSupport S
      haveI : Nonempty ↥Y := pointSupportNonempty S hm
      let HY := hypothesisEnvelope L c Y
      let hrow := good_on_support_gives_row_response L c hreal.choose_spec.1 Y HY rfl
      haveI : Nonempty ↥HY := let ⟨h, _⟩ := hrow (uniformPMF ↥Y); ⟨h⟩
      let M : ↥HY → ↥Y → Bool := fun h y => decide (h.val (y : X) = c (y : X))
      let p : FinitePMF ↥HY := (mwu_approx_minimax M (2 / 3) (1 / 12) (by norm_num) hrow).choose
      let hvc_bound := agreeTests_boolVCDim_le C c Y HY
        (fun h hh => hypothesisEnvelope_sub L c Y h hh) (le_of_eq hd.symm)
      (hVCApprox (agreeTests c Y HY) hvc_bound p).choose
  let compressCore : {m : ℕ} → (Fin m → X × Bool) →
      Finset (X × Bool) × IncidenceInfo Tvc Kreal :=
    fun {m} S =>
      if hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2 then
        let c := hreal.choose; let Y := pointSupport S
        if hm : 0 < m then
          haveI : Nonempty ↥Y := pointSupportNonempty S hm
          let HY := hypothesisEnvelope L c Y
          haveI : Nonempty ↥HY :=
            let hrow := good_on_support_gives_row_response L c hreal.choose_spec.1 Y HY rfl
            let ⟨h, _⟩ := hrow (uniformPMF ↥Y); ⟨h⟩
          let reps : Fin Tvc → ↥HY := mkReps S hreal hm
          let getWitness : Fin Tvc → Finset X := fun t =>
            (Finset.mem_image.mp (reps t).property).choose
          let kernel : Finset (X × Bool) :=
            Finset.univ.biUnion (fun t => (getWitness t).image (fun x => (x, c x)))
          (kernel, fun t => encodeWitnessInfo kernel c Kreal (getWitness t))
        else (∅, fun _ => ∅)
      else (∅, fun _ => ∅)
  let blockHyp := moranBlockHyp L (T := Tvc) (K := Kreal)
  let rowHyp : {m : ℕ} → (S : Fin m → X × Bool) →
      (∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2) → Fin Tvc → X → Bool :=
    fun {m} S _hreal t x => blockHyp (compressCore S).1 (compressCore S).2 t x
  have hsmall : ∀ {m : ℕ} (S : Fin m → X × Bool),
      (compressCore S).1.card ≤ Kreal := by
    intro m S; dsimp only [compressCore]
    split
    · next hreal =>
      split
      · next hm =>
        have hwitness_bound : ∀ (h : ↥(hypothesisEnvelope L hreal.choose (pointSupport S))),
            (Finset.mem_image.mp h.property).choose.card ≤ s := fun h =>
          (Finset.mem_filter.mp (Finset.mem_image.mp h.property).choose_spec.1).2
        apply Finset.card_biUnion_le.trans
        apply le_trans _ (show Finset.univ.sum (fun _ : Fin Tvc => s) ≤ Kreal by
          simp [Finset.sum_const, Fintype.card_fin, Kreal])
        apply Finset.sum_le_sum; intro t _
        exact Finset.card_image_le.trans (hwitness_bound _)
      · next => simp
    · next => simp
  have hsub : ∀ {m : ℕ} (S : Fin m → X × Bool),
      ↑(compressCore S).1 ⊆ Set.range S := by
    intro m S p hp; dsimp only [compressCore] at hp
    split at hp
    · next hreal =>
      split at hp
      · next hm =>
        rw [Finset.mem_coe, Finset.mem_biUnion] at hp
        obtain ⟨t, _, hp2⟩ := hp
        rw [Finset.mem_image] at hp2; obtain ⟨x, hxw, hpx⟩ := hp2
        have hgw : ∀ (h : ↥(hypothesisEnvelope L hreal.choose (pointSupport S))),
            (Finset.mem_image.mp h.property).choose ⊆ pointSupport S := by
          intro h
          exact Finset.mem_powerset.mp
            (Finset.mem_filter.mp (Finset.mem_image.mp h.property).choose_spec.1).1
        have hxY := hgw _ hxw
        simp only [pointSupport, Finset.mem_image, Finset.mem_univ, true_and] at hxY
        obtain ⟨i, hi⟩ := hxY
        exact ⟨i, by rw [← hpx, Prod.mk.injEq]; exact ⟨hi, (hreal.choose_spec.2 i).symm ▸
          congrArg hreal.choose hi⟩⟩
      · next => simp at hp
    · next => simp at hp
  have hagree : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m) (t : Fin Tvc),
      blockHyp (compressCore S).1 (compressCore S).2 t (S i).1 =
        rowHyp S hreal t (S i).1 := by
    intro m S hreal i t; rfl
  have hmajor : ∀ {m : ℕ} (S : Fin m → X × Bool)
      (hreal : ∃ c ∈ C, ∀ i : Fin m, c (S i).1 = (S i).2)
      (i : Fin m),
      ((∑ t : Fin Tvc,
          if rowHyp S hreal t (S i).1 = (S i).2 then (1 : ℝ) else 0) / Tvc) >
        (1 / 2 : ℝ) := by
    intro m S hreal i
    have hm : 0 < m := Fin.pos i
    have h_kernel_labels : ∀ pair ∈ (compressCore S).1,
        pair.2 = hreal.choose pair.1 := by
      dsimp only [compressCore, pointSupportNonempty]
      simp only [dif_pos hreal, dif_pos hm]
      simpa using moranKernel_labels hreal.choose
        (fun t => (Finset.mem_image.mp (mkReps S hreal hm t).property).choose)
    have hround : ∀ t : Fin Tvc,
        rowHyp S hreal t (S i).1 = (mkReps S hreal hm t).val (S i).1 := by
      intro t
      let c : X → Bool := hreal.choose
      let reps := mkReps S hreal hm
      let W : Finset X := (Finset.mem_image.mp (reps t).property).choose
      have hWker : ∀ x ∈ W, (x, c x) ∈ (compressCore S).1 := fun x hx => by
        dsimp only [compressCore, pointSupportNonempty]
        simpa only [dif_pos hreal, dif_pos hm] using witness_mem_moranKernel c _ t hx
      have hinfo_eq : (compressCore S).2 t = encodeWitnessInfo (compressCore S).1 c Kreal W := by
        dsimp only [compressCore, pointSupportNonempty, c, reps, W]
        simp only [dif_pos hreal, dif_pos hm]
      dsimp only [rowHyp, blockHyp, moranBlockHyp]
      rw [hinfo_eq]
      exact roundtrip_blockHyp_eq_rep (learn := fun {m} => L.learn)
        (kernel := (compressCore S).1) (c := c) (K := Kreal) (W := W)
        (h := (reps t).val) (hsmall S) hWker h_kernel_labels
        ((Finset.mem_image.mp (reps t).property).choose_spec.2) (x := (S i).1)
    have hsum_eq : (∑ t : Fin Tvc,
        if rowHyp S hreal t (S i).1 = (S i).2 then (1 : ℝ) else 0) =
      (∑ t : Fin Tvc,
        if (mkReps S hreal hm t).val (S i).1 = hreal.choose (S i).1
        then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl (fun t _ =>
        if_congr (by rw [hround t, (hreal.choose_spec.2 i).symm]) rfl rfl)
    rw [hsum_eq]
    suffices h_ge : (∑ t : Fin Tvc,
        if (mkReps S hreal hm t).val (S i).1 = hreal.choose (S i).1
        then (1 : ℝ) else 0) / ↑Tvc ≥ 13 / 24 by linarith
    haveI hYne : Nonempty ↥(pointSupport S) := pointSupportNonempty S hm
    let c' := hreal.choose
    let Y' := pointSupport S
    let HY' := hypothesisEnvelope L c' Y'
    let hrow' := good_on_support_gives_row_response L c' hreal.choose_spec.1 Y' HY' rfl
    haveI hHYne : Nonempty ↥HY' := let ⟨h, _⟩ := hrow' (uniformPMF ↥Y'); ⟨h⟩
    let M' : ↥HY' → ↥Y' → Bool := fun h y => decide (h.val (y : X) = c' (y : X))
    let mwu_result := mwu_approx_minimax M' (2 / 3) (1 / 12) (by norm_num) hrow'
    let p := mwu_result.choose
    have hp : ∀ y : ↥Y', (2 : ℝ) / 3 - 1 / 12 ≤ boolGamePayoff M' p y := mwu_result.choose_spec
    let hvc_bound := agreeTests_boolVCDim_le C c' Y' HY'
      (fun h hh => hypothesisEnvelope_sub L c' Y' h hh) (le_of_eq hd.symm)
    let vc_result := hVCApprox (agreeTests c' Y' HY') hvc_bound p
    have hreps : ∀ a ∈ agreeTests c' Y' HY',
        |boolTestExpectation p a -
          boolTestExpectation (empiricalPMF hTvcPos (mkReps S hreal hm)) a| ≤ 1 / 24 :=
      fun a ha => by convert vc_result.choose_spec a ha using 3
    have hxi_in_Y : (S i).1 ∈ Y' := by
      simp only [Y', pointSupport, Finset.mem_image, Finset.mem_univ, true_and]; exact ⟨i, rfl⟩
    have hat_mem : agreeTest c' (S i).1 HY' ∈ agreeTests c' Y' HY' :=
      Finset.mem_image.mpr ⟨(S i).1, hxi_in_Y, rfl⟩
    have h_minimax : boolTestExpectation p (agreeTest c' (S i).1 HY') ≥ 7 / 12 := by
      have h_gp := hp ⟨(S i).1, hxi_in_Y⟩
      rw [boolGamePayoff_eq_boolTestExpectation,
        show (fun h => M' h ⟨(S i).1, hxi_in_Y⟩) = agreeTest c' (S i).1 HY' from
          funext (fun h => by simp only [M', agreeTest])] at h_gp
      linarith
    have h_emp_ge : boolTestExpectation (empiricalPMF hTvcPos (mkReps S hreal hm))
        (agreeTest c' (S i).1 HY') ≥ 13 / 24 := by
      have ⟨_, h_hi⟩ := abs_le.mp (hreps (agreeTest c' (S i).1 HY') hat_mem); linarith
    linarith [boolTestExpectation_empirical_agreeTest_eq_avg
      hTvcPos (mkReps S hreal hm) c' (S i).1]
  exact finalizeIncidenceScheme Tvc Kreal compressCore blockHyp rowHyp
    hTvcPos hsmall hsub hagree hmajor
/-! ## Forward direction: VCDim < ⊤ → compression with info -/

theorem vcdim_finite_imp_compression_with_info
    (X : Type u) (C : ConceptClass X Bool) (hC : VCDim X C < ⊤) :
    ∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k := by
  by_cases hne : C.Nonempty
  · obtain ⟨L, _⟩ := vcdim_finite_imp_proper_finite_support_learner X C hne hC
    exact moran_yehudayoff_forward_construction X C hne L hC L.sampleBound
  · refine ⟨1, ?_, ?_⟩
    · exact {
        Info := PUnit
        info_finite := inferInstance
        compress := fun _ => (∅, PUnit.unit)
        reconstruct := fun _ _ _ => false
        kernelSize := 0
        compress_small := fun _ => by simp
        compress_sub := fun _ x hx => by simp at hx
        correct := fun {m} S hreal => by
          exfalso; obtain ⟨c, hcC, _⟩ := hreal; exact hne ⟨c, hcC⟩
      }
    · simp [CompressionSchemeWithInfo.size]

/-! ## Reverse direction: compression with info → VCDim < ⊤ -/

/-- Pigeonhole core: if two C-realizable samples over the same points with
    different labelings produce the same (kernel, info) pair, correctness
    forces the labelings to agree. -/
theorem compress_with_info_injective_on_labelings {X : Type u} {n : ℕ}
    {C : ConceptClass X Bool}
    (cs : CompressionSchemeWithInfo X Bool C)
    (pts : Fin n → X) (_hpts : Function.Injective pts)
    (f g : Fin n → Bool)
    (hf_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i)
    (hg_real : ∃ c ∈ C, ∀ i : Fin n, c (pts i) = g i)
    (hfg : cs.compress (fun i => (pts i, f i)) = cs.compress (fun i => (pts i, g i))) :
    f = g := by
  funext i
  have mk_real : ∀ (h : Fin n → Bool), (∃ c ∈ C, ∀ i : Fin n, c (pts i) = h i) →
      ∃ c ∈ C, ∀ j : Fin n, c ((fun j => (pts j, h j)) j).1 = ((fun j => (pts j, h j)) j).2 :=
    fun h ⟨c, hcC, hc⟩ => ⟨c, hcC, fun j => by simp [hc j]⟩
  have hf := cs.correct (fun j => (pts j, f j)) (mk_real f hf_real) i
  have hg := cs.correct (fun j => (pts j, g j)) (mk_real g hg_real) i
  simp only at hf hg
  rw [← hf, congr_fun (show cs.reconstruct (cs.compress (fun j => (pts j, f j))).1
    (cs.compress (fun j => (pts j, f j))).2 =
    cs.reconstruct (cs.compress (fun j => (pts j, g j))).1
    (cs.compress (fun j => (pts j, g j))).2 from by rw [hfg]) (pts i), hg]

private lemma shatters_subset_compression {X : Type u} {C : ConceptClass X Bool}
    {S T : Finset X} (hST : T ⊆ S) (hS : Shatters X C S) : Shatters X C T := by
  intro f
  let g : ↥S → Bool := fun ⟨x, hx⟩ => if h : x ∈ T then f ⟨x, h⟩ else false
  obtain ⟨c, hcC, hcg⟩ := hS g
  exact ⟨c, hcC, fun ⟨x, hx⟩ => by
    have := hcg ⟨x, hST hx⟩; simp only [g, hx, dite_true] at this; exact this⟩

private lemma succ_le_two_pow_compression (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc k + 1 + 1 ≤ 2 ^ k + 2 ^ k := by omega
                   _ = 2 ^ (k + 1) := by ring

/-- Exponential beats polynomial for the compression pigeonhole argument. -/
private lemma exp_beats_poly_compression (s : ℕ) :
    (s + 1) ^ 2 * (4 * (s + 1) ^ 2) ^ s < 2 ^ (2 * (s + 1) * (s + 1)) := by
  have h1 : (s + 1) ^ 2 * (4 * (s + 1) ^ 2) ^ s =
      (s + 1) ^ (2 * s + 2) * 4 ^ s := by rw [mul_pow, ← pow_mul]; ring_nf
  have h2 : (s + 1) ^ (2 * s + 2) ≤ (2 ^ s) ^ (2 * s + 2) :=
    Nat.pow_le_pow_left (succ_le_two_pow_compression s) _
  rw [h1, show (4 : ℕ) ^ s = 2 ^ (2 * s) from by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num, ← pow_mul]]
  calc (s + 1) ^ (2 * s + 2) * 2 ^ (2 * s)
      ≤ (2 ^ s) ^ (2 * s + 2) * 2 ^ (2 * s) := Nat.mul_le_mul_right _ h2
    _ = 2 ^ (2 * s ^ 2 + 4 * s) := by rw [← pow_mul, ← pow_add]; ring_nf
    _ < 2 ^ (2 * (s + 1) * (s + 1)) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

theorem compression_with_info_imp_vcdim_finite
    (X : Type u) (C : ConceptClass X Bool)
    (hcomp : ∃ (k : ℕ) (cs : CompressionSchemeWithInfo X Bool C), cs.size = k) :
    VCDim X C < ⊤ := by
  by_contra h_top
  push Not at h_top; rw [top_le_iff] at h_top
  obtain ⟨k, cs, hk⟩ := hcomp
  have h_large : ∀ n : ℕ, ∃ S : Finset X, Shatters X C S ∧ n ≤ S.card := by
    intro n; by_contra h_neg; push Not at h_neg
    have : VCDim X C ≤ ↑n := iSup₂_le fun S hS =>
      mod_cast Nat.le_of_lt_succ (Nat.lt_succ_of_lt (h_neg S hS))
    exact absurd h_top (ne_of_lt (lt_of_le_of_lt this (WithTop.coe_lt_top _)))
  set K := cs.kernelSize with hK_def
  set I := @Fintype.card cs.Info cs.info_finite with hI_def
  set s := K + I
  set N := 2 * (s + 1) * (s + 1)
  obtain ⟨T₀, hT₀_shatt, hT₀_card⟩ := h_large N
  haveI : DecidableEq X := Classical.decEq X
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hT₀_card
  have hT_shatt : Shatters X C T := shatters_subset_compression hT_sub hT₀_shatt
  set n := T.card
  have hn_eq : n = N := hT_card
  let eqv := T.equivFin.symm
  let pts : Fin n → X := fun i => (eqv i : X)
  let mkSample : (Fin n → Bool) → (Fin n → X × Bool) := fun f i => (pts i, f i)
  have h_realizable : ∀ f : Fin n → Bool, ∃ c ∈ C, ∀ i : Fin n, c (pts i) = f i := by
    intro f
    let f' : ↥T → Bool := fun ⟨x, hx⟩ => f (T.equivFin ⟨x, hx⟩)
    obtain ⟨c, hcC, hcf'⟩ := hT_shatt f'
    exact ⟨c, hcC, fun i => by
      have := hcf' (eqv i); simp only [f', pts] at this ⊢
      rwa [T.equivFin.apply_symm_apply i] at this⟩
  have h_inj : Function.Injective (cs.compress ∘ mkSample) :=
    fun f g hfg => compress_with_info_injective_on_labelings cs pts
      (fun _ _ h => eqv.injective (Subtype.val_injective h)) f g
      (h_realizable f) (h_realizable g) hfg
  set A := T ×ˢ (Finset.univ : Finset Bool) with hA_def
  set target := (A.powerset.filter (fun S => S.card ≤ K)) ×ˢ
    (@Finset.univ cs.Info cs.info_finite) with htarget_def
  have h_maps_to : ∀ f : Fin n → Bool, (cs.compress ∘ mkSample) f ∈ target := by
    intro f
    simp only [Function.comp, htarget_def, Finset.mem_product, Finset.mem_filter,
      Finset.mem_powerset, Finset.mem_univ, and_true]
    constructor
    · intro p hp
      obtain ⟨i, hi⟩ := cs.compress_sub (mkSample f) (Finset.mem_coe.mpr hp)
      simp only [mkSample] at hi
      rw [Finset.mem_product]
      exact ⟨by rw [show p.1 = pts i from (congr_arg Prod.fst hi).symm]; exact (eqv i).2,
             Finset.mem_univ _⟩
    · exact cs.compress_small (mkSample f)
  have hA_card : A.card = 2 * n := by
    simp only [hA_def, Finset.card_product, Finset.card_univ, Fintype.card_bool]; ring
  have hn_pos : 0 < n := by rw [hn_eq]; positivity
  have h_target_card : target.card ≤ (K + 1) * (2 * n) ^ K * I := by
    simp only [htarget_def, Finset.card_product, Finset.card_univ, ← hI_def]
    apply Nat.mul_le_mul_right
    calc (A.powerset.filter (fun S => S.card ≤ K)).card
        ≤ (Finset.range (K + 1)).sum (fun j => (A.powersetCard j).card) := by
          apply (Finset.card_le_card _).trans Finset.card_biUnion_le
          intro S hS
          simp only [Finset.mem_filter, Finset.mem_powerset] at hS
          obtain ⟨hSA, hSK⟩ := hS
          exact Finset.mem_biUnion.mpr
            ⟨S.card, by simp only [Finset.mem_range]; omega,
             Finset.mem_powersetCard.mpr ⟨hSA, rfl⟩⟩
      _ = (Finset.range (K + 1)).sum (fun j => (2 * n).choose j) := by
          congr 1; ext j; simp [Finset.card_powersetCard, hA_card]
      _ ≤ (Finset.range (K + 1)).sum (fun _ => (2 * n) ^ K) := by
          apply Finset.sum_le_sum; intro j hj
          simp only [Finset.mem_range] at hj
          exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right (by omega) (by omega))
      _ = (K + 1) * (2 * n) ^ K := by simp [Finset.sum_const, Finset.card_range]
  have h_target_lt : target.card < 2 ^ n := by
    have hn_val : n = 2 * (s + 1) * (s + 1) := hn_eq
    calc target.card
        ≤ (K + 1) * (2 * n) ^ K * I := h_target_card
      _ ≤ (s + 1) * (2 * n) ^ s * (s + 1) := by
          apply Nat.mul_le_mul
            (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))) (by omega)
      _ = (s + 1) ^ 2 * (2 * n) ^ s := by ring
      _ = (s + 1) ^ 2 * (2 * (2 * (s + 1) * (s + 1))) ^ s := by rw [hn_val]
      _ = (s + 1) ^ 2 * (4 * (s + 1) ^ 2) ^ s := by ring_nf
      _ < 2 ^ (2 * (s + 1) * (s + 1)) := exp_beats_poly_compression s
      _ = 2 ^ n := by rw [hn_val]
  have h_card_lt : target.card < (Finset.univ : Finset (Fin n → Bool)).card := by
    have : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
      simp [Fintype.card_fin, Fintype.card_bool]
    rw [this]; exact h_target_lt
  exact absurd h_inj (by
    intro h_inj_false
    obtain ⟨f, _, g, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt (fun x _ => h_maps_to x)
    exact absurd heq (fun h => hne (h_inj_false h)))

/-! ## Biconditional -/

theorem fundamental_vc_compression_with_info
    (X : Type u) (C : ConceptClass X Bool) :
    (VCDim X C < ⊤) ↔
    (∃ (k : ℕ) (cs : CompressionSchemeWithInfo0 X Bool C), cs.size = k) :=
  ⟨vcdim_finite_imp_compression_with_info X C,
   fun ⟨k, cs, hk⟩ => compression_with_info_imp_vcdim_finite X C ⟨k, cs, hk⟩⟩

end -- noncomputable section
