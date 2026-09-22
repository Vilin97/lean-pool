/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.SymmetricGauge
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.SchattenGauge
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.SupGauge
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Isometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.Basic
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Adjoint
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.KyFanDominance
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.DiagonalSequence
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.Schatten

/-!
# Operator ideal families induced by symmetric gauges

A single scalar-free `SymmetricGauge` induces rectangular families over every
`RCLike` field, with independent source and target universes. The four ideal laws
come from approximation numbers and the dominated-sequence extension. Ky Fan
dominance is a property of this base family. Adjoint symmetry exchanges the two
universes; the diagonal view packages that law without redefining the gauge.

Finite-exponent Schatten families and the supremum endpoint are instances of the
same construction. The power-sum identification supplies their completeness and
the trace-class and Hilbert--Schmidt identifications.
-/

public section

open scoped NNReal ENNReal

namespace TauCeti

universe u v w

open _root_.ContinuousLinearMap

variable {𝕜 : Type u} [RCLike 𝕜]

variable (Φ : SymmetricGauge)

/-- The inner product of a universe lift, carried across `ULift.down`.

Mathlib lifts the normed group and normed space structures to `ULift` but not the inner
product, and the rectangular ideal families carry their source and target in *independent*
universes, so realizing a model operator there needs this.  Local: a global instance would
put an inner product on every `ULift` in the import graph. -/
noncomputable local instance uliftInnerProductSpace {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :
    InnerProductSpace 𝕜 (ULift.{v} E) where
  inner x y := inner 𝕜 x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := 𝕜) x.down
  conj_inner_symm x y := inner_conj_symm (𝕜 := 𝕜) x.down y.down
  add_left x y z := inner_add_left (𝕜 := 𝕜) x.down y.down z.down
  smul_left x y r := inner_smul_left (𝕜 := 𝕜) x.down y.down r

/-- The approximation-number sequence of an operator, in `ℝ≥0∞`. -/
noncomputable def approxSeq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (A : E →L[𝕜] F) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (A.approximationNumber n)

/-- The approximation-number sequence is antitone. -/
theorem approxSeq_antitone {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (A : E →L[𝕜] F) : Antitone (approxSeq A) := by
  intro m n hmn
  exact ENNReal.ofReal_le_ofReal (A.approximationNumber_antitone hmn)

/-- Every approximation number is finite, so `approxSeq` never takes the value
`⊤`.  This is what lets the `ℝ≥0∞` reductions in `SymmetricGauge` fire. -/
theorem approxSeq_ne_top {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (A : E →L[𝕜] F) (n : ℕ) : approxSeq A n ≠ ⊤ :=
  ENNReal.ofReal_ne_top

section Laws

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Prefix sums of `approxSeq (A + B)` are dominated by those of the sum
sequence.  This is `kyFanGauge_add_le` pushed into `ℝ≥0∞`. -/
theorem approxSeq_prefix_add_le (A B : E →L[𝕜] F) (k : ℕ) :
    ∑ n ∈ Finset.range k, approxSeq (A + B) n
      ≤ ∑ n ∈ Finset.range k, (approxSeq A n + approxSeq B n) := by
  have hky := ContinuousLinearMap.kyFanGauge_add_le A B k
  simp only [ContinuousLinearMap.kyFanGauge] at hky
  -- Both sides are `ofReal` of a finite sum of nonnegative reals.
  have hL : ∑ n ∈ Finset.range k, approxSeq (A + B) n
      = ENNReal.ofReal (∑ n ∈ Finset.range k, (A + B).approximationNumber n) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · rfl
    · exact fun i _ => (A + B).approximationNumber_nonneg i
  have hR : ∑ n ∈ Finset.range k, (approxSeq A n + approxSeq B n)
      = ENNReal.ofReal ((∑ n ∈ Finset.range k, A.approximationNumber n)
          + ∑ n ∈ Finset.range k, B.approximationNumber n) := by
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => A.approximationNumber_nonneg i)
      (Finset.sum_nonneg fun i _ => B.approximationNumber_nonneg i),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => A.approximationNumber_nonneg i),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => B.approximationNumber_nonneg i),
      ← Finset.sum_add_distrib]
    rfl
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal hky

/-- **Subadditivity of the induced gauge.**  The only law needing two `extend`
lemmas: majorization first, then splitting. -/
theorem extend_approxSeq_add_le (A B : E →L[𝕜] F) :
    Φ.extend (approxSeq (A + B)) ≤ Φ.extend (approxSeq A) + Φ.extend (approxSeq B) := by
  have hmaj : Φ.extend (approxSeq (A + B))
      ≤ Φ.extend (fun n => approxSeq A n + approxSeq B n) :=
    Φ.extend_le_extend_of_forall_sum_le (approxSeq_antitone (A + B))
      (approxSeq_prefix_add_le A B)
  exact hmaj.trans (Φ.extend_add_le _ _)

omit [CompleteSpace E] [CompleteSpace F] in
/-- **Homogeneity of the induced gauge.** -/
theorem extend_approxSeq_smul (c : 𝕜) (A : E →L[𝕜] F) :
    Φ.extend (approxSeq (c • A)) = ‖c‖ₑ * Φ.extend (approxSeq A) := by
  have hseq : approxSeq (c • A) = fun n => ((‖c‖₊ : ℝ≥0) : ℝ≥0∞) * approxSeq A n := by
    funext n
    simp only [approxSeq, ContinuousLinearMap.approximationNumber_smul]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    rfl
  rw [hseq, Φ.extend_smul]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The gauge dominates the operator norm**, via `a₀ T = ‖T‖`. -/
theorem enorm_le_extend_approxSeq (A : E →L[𝕜] F) :
    ‖A‖ₑ ≤ Φ.extend (approxSeq A) := by
  have h0 : approxSeq A 0 = ‖A‖ₑ := by
    simp only [approxSeq, ContinuousLinearMap.approximationNumber_index_zero]
    rw [← ofReal_norm]
  calc ‖A‖ₑ = approxSeq A 0 := h0.symm
    _ ≤ Φ.extend (approxSeq A) := Φ.le_extend _ 0

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The composition bound.**  `approxSeq` of `L ∘L A ∘L R` is dominated
termwise by `‖L‖ * ‖R‖` times `approxSeq A`, and `extend_mono` plus
`extend_smul` turn that into the gauge statement. -/
theorem extend_approxSeq_comp_le {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    Φ.extend (approxSeq (L ∘L A ∘L R)) ≤ ‖L‖ₑ * Φ.extend (approxSeq A) * ‖R‖ₑ := by
  have hterm : ∀ n, approxSeq (L ∘L A ∘L R) n
      ≤ ((‖L‖₊ * ‖R‖₊ : ℝ≥0) : ℝ≥0∞) * approxSeq A n := by
    intro n
    have h1 : (L ∘L A ∘L R).approximationNumber n ≤ ‖L‖ * ((A ∘L R).approximationNumber n) :=
      ContinuousLinearMap.approximationNumber_comp_le_norm_mul L (A ∘L R) n
    have h2 : (A ∘L R).approximationNumber n ≤ A.approximationNumber n * ‖R‖ :=
      ContinuousLinearMap.approximationNumber_comp_le_mul_norm A R n
    have hchain : (L ∘L A ∘L R).approximationNumber n
        ≤ (‖L‖ * ‖R‖) * A.approximationNumber n := by
      calc (L ∘L A ∘L R).approximationNumber n
          ≤ ‖L‖ * ((A ∘L R).approximationNumber n) := h1
        _ ≤ ‖L‖ * (A.approximationNumber n * ‖R‖) := by gcongr
        _ = (‖L‖ * ‖R‖) * A.approximationNumber n := by ring
    simp only [approxSeq]
    calc ENNReal.ofReal ((L ∘L A ∘L R).approximationNumber n)
        ≤ ENNReal.ofReal ((‖L‖ * ‖R‖) * A.approximationNumber n) :=
          ENNReal.ofReal_le_ofReal hchain
      _ = ((‖L‖₊ * ‖R‖₊ : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (A.approximationNumber n) := by
          rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal]
          congr 1
  calc Φ.extend (approxSeq (L ∘L A ∘L R))
      ≤ Φ.extend (fun n => ((‖L‖₊ * ‖R‖₊ : ℝ≥0) : ℝ≥0∞) * approxSeq A n) :=
        Φ.extend_mono hterm
    _ = ((‖L‖₊ * ‖R‖₊ : ℝ≥0) : ℝ≥0∞) * Φ.extend (approxSeq A) :=
        Φ.extend_smul (‖L‖₊ * ‖R‖₊) (approxSeq A)
    _ = ‖L‖ₑ * Φ.extend (approxSeq A) * ‖R‖ₑ := by
        simp only [enorm_eq_nnnorm, ENNReal.coe_mul]
        ring

end Laws

/-- **The operator ideal family induced by a symmetric gauge.**

`gauge A = Φ∞ (a(A))`: the extended gauge applied to the approximation-number
sequence.  The four laws are the four theorems above, each of which is one
approximation-number fact composed with one law of `SymmetricGauge.extend`. -/
@[expose]
noncomputable def symmetricGaugeFamily (𝕜 : Type u) [RCLike 𝕜]
    (Φ : SymmetricGauge) :
    OperatorIdealFamily.{u, v, w} 𝕜 where
  gauge A := Φ.extend (approxSeq A)
  gauge_add_le A B := extend_approxSeq_add_le Φ A B
  gauge_smul c A := extend_approxSeq_smul Φ c A
  enorm_le_gauge A := enorm_le_extend_approxSeq Φ A
  gauge_comp_le L A R := extend_approxSeq_comp_le Φ L A R

/-- The induced family's gauge unfolds to the extended gauge of the
approximation-number sequence. -/
@[simp]
theorem symmetricGaugeFamily_gauge {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (symmetricGaugeFamily 𝕜 Φ).gauge A = Φ.extend (approxSeq A) := rfl

/-- Equality of the induced families forces agreement on antitone sequences.

A bounded sequence is realized by a diagonal operator. Scalar transport first
places that model over the requested field without raising its carrier universe;
independent universe lifts then place it in the family's domain and codomain.
For an unbounded sequence both extensions are infinite. -/
theorem symmetricGaugeFamily_injective {Phi Psi : SymmetricGauge}
    (h : symmetricGaugeFamily.{u, v, w} 𝕜 Phi =
      symmetricGaugeFamily.{u, v, w} 𝕜 Psi)
    {a : ℕ → ENNReal} (ha : Antitone a) :
    Phi.extend a = Psi.extend a := by
  classical
  by_cases hbdd : ∃ B : NNReal, ∀ n, a n ≤ (B : ENNReal)
  · obtain ⟨B, hB⟩ := hbdd
    have hafin : ∀ n, a n ≠ ⊤ := fun n =>
      ne_top_of_le_ne_top (by simp) (hB n)
    have realize {L : Type} [RCLike L] (e : RCLikeIso L 𝕜) :
        Phi.extend a = Psi.extend a := by
      let c : ℕ → L := fun n => ((a n).toReal : L)
      have hcnorm : ∀ n, ‖c n‖ = (a n).toReal := by
        intro n
        simp [c, abs_of_nonneg ENNReal.toReal_nonneg]
      have hB0 : (0 : ℝ) ≤ (B : ℝ) := B.coe_nonneg
      have hcB : ∀ n, ‖c n‖ ≤ (B : ℝ) := by
        intro n
        rw [hcnorm]
        exact (ENNReal.toReal_le_toReal (hafin n) (by simp)).2 (hB n)
      have hanti : Antitone fun n => ‖c n‖ := by
        intro i j hij
        simp only [hcnorm]
        exact (ENNReal.toReal_le_toReal (hafin j) (hafin i)).2 (ha hij)
      let H := ScalarTransport e (lp (fun _ : ℕ => L) 2)
      let Q : H →L[𝕜] H := ScalarTransport.clm (e := e) (diagOpLp c hB0 hcB)
      let ev : ULift.{v, 0} H ≃ₗᵢ[𝕜] H := LinearIsometryEquiv.ulift 𝕜 H
      let ew : H ≃ₗᵢ[𝕜] ULift.{w, 0} H :=
        (LinearIsometryEquiv.ulift 𝕜 H).symm
      let T : ULift.{v, 0} H →L[𝕜] ULift.{w, 0} H :=
        ew.toLinearIsometry.toContinuousLinearMap ∘L Q ∘L
          ev.toLinearIsometry.toContinuousLinearMap
      have hseq : approxSeq T = a := by
        funext n
        simp only [approxSeq, T, Q]
        rw [approximationNumber_comp_linearIsometryEquiv,
          ScalarTransport.approximationNumber_clm,
          approximationNumber_diagOpLp c hB0 hcB hanti n, hcnorm,
          ENNReal.ofReal_toReal (hafin n)]
      have hop := congrArg (fun N : OperatorIdealFamily.{u, v, w} 𝕜 => N.gauge T) h
      simpa only [symmetricGaugeFamily_gauge, hseq] using hop
    rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with hI | hI
    · exact realize (RCLikeIso.real hI).symm
    · exact realize (RCLikeIso.complex hI).symm
  · push Not at hbdd
    have hsup : (⨆ n, a n) = ⊤ := by
      refine iSup_eq_top.2 fun b hb => ?_
      lift b to NNReal using hb.ne
      obtain ⟨n, hn⟩ := hbdd b
      exact ⟨n, hn⟩
    have hinf : ∀ Theta : SymmetricGauge, Theta.extend a = ⊤ := fun Theta =>
      top_le_iff.1 (hsup ▸ Theta.iSup_le_extend a)
    rw [hinf Phi, hinf Psi]

/-- The extended finite-sequence Schatten gauge is the power-sum norm. -/
theorem extend_approxSeq_schattenGauge {p : ℝ} (hp : 1 ≤ p) {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (T : E →L[𝕜] F) :
    (schattenGauge p hp).extend (approxSeq T)
      = ContinuousLinearMap.schattenENorm p T := by
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans_le hp
  have hinv : (0 : ℝ) < 1 / p := by positivity
  have hnn : ∀ n, 0 ≤ T.approximationNumber n := fun n =>
    ContinuousLinearMap.approximationNumber_nonneg T n
  rw [show approxSeq T = fun n => ENNReal.ofReal (T.approximationNumber n) from rfl,
    (schattenGauge p hp).extend_eq_iSup_ofFin hnn,
    ContinuousLinearMap.schattenENorm, ENNReal.tsum_eq_iSup_nat, ← one_div,
    iSup_rpow _ hinv]
  refine iSup_congr fun k => ?_
  rw [show (schattenGauge p hp)
        (SymmetricGauge.ofFin (fun i : Fin k => T.approximationNumber i))
      = schattenGaugeFun p
        (SymmetricGauge.ofFin (fun i : Fin k => T.approximationNumber i)) from rfl,
    schattenGaugeFun_ofFin hp0 hnn k]
  rw [ENNReal.coe_rpow_of_nonneg _ hinv.le, ENNReal.ofNNReal_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ENNReal.coe_rpow_of_nonneg _ hp0.le, ENNReal.ofNNReal_toNNReal]

/-! ## Adjoint symmetry and rectangular Ky Fan dominance -/

section Symmetric

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The gauge is unchanged by passing to the adjoint. -/
theorem extend_approxSeq_adjoint (A : E →L[𝕜] F) :
    Φ.extend (approxSeq (ContinuousLinearMap.adjoint A)) = Φ.extend (approxSeq A) := by
  congr 1
  funext n
  simp only [approxSeq, ContinuousLinearMap.approximationNumber_adjoint]

end Symmetric

/-- Adjoint invariance across independently chosen source and target universes. -/
theorem gauge_adjoint_symmetricGaugeFamily
    {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (symmetricGaugeFamily.{u, w, v} 𝕜 Φ).gauge A.adjoint =
      (symmetricGaugeFamily.{u, v, w} 𝕜 Φ).gauge A :=
  extend_approxSeq_adjoint Φ A

/-- The adjoint-invariant diagonal view of the rectangular family. -/
noncomputable def symmetricGaugeFamilySymmetric (𝕜 : Type u) [RCLike 𝕜]
    (Φ : SymmetricGauge) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := symmetricGaugeFamily.{u, v, v} 𝕜 Φ
  gauge_adjoint A := gauge_adjoint_symmetricGaugeFamily Φ A

/-- **Milestone B2.**  A family induced by a symmetric gauge is Ky Fan dominant.

The hypothesis `∀ k, A.kyFanGauge k ≤ B.kyFanGauge k` *is* prefix-sum domination
of the approximation-number sequences, which is exactly what
`SymmetricGauge.extend_le_extend_of_forall_sum_le` consumes.  Only the first sequence needs
antitonicity, supplied by
`approximationNumber_antitone`.

So no part of the Hardy--Littlewood--Pólya argument appears here: it was done
once, at the level of sequences, and this instance is its transport. -/
instance isKyFanDominant_symmetricGaugeFamily :
    IsKyFanDominant (symmetricGaugeFamily.{u, v, w} 𝕜 Φ) where
  gauge_le_of_forall_kyFanGauge_le {E F _ _ _ _ _ _} {A B} h := by
    have hpre : ∀ k, ∑ n ∈ Finset.range k, approxSeq A n
        ≤ ∑ n ∈ Finset.range k, approxSeq B n := by
      intro k
      have hk := h k
      simp only [ContinuousLinearMap.kyFanGauge] at hk
      rw [show (∑ n ∈ Finset.range k, approxSeq A n)
            = ENNReal.ofReal (∑ n ∈ Finset.range k, A.approximationNumber n) by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun i _ => A.approximationNumber_nonneg i)]; rfl,
        show (∑ n ∈ Finset.range k, approxSeq B n)
            = ENNReal.ofReal (∑ n ∈ Finset.range k, B.approximationNumber n) by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun i _ => B.approximationNumber_nonneg i)]; rfl]
      exact ENNReal.ofReal_le_ofReal hk
    exact Φ.extend_le_extend_of_forall_sum_le (approxSeq_antitone A) hpre

/-! ## The Schatten scale

The Schatten classes are *obtained* from the symmetric-gauge construction rather
than built separately, which is the roadmap's point: their four laws are the
family's and not new work.
-/

/-- The rectangular Schatten family induced by the finite-exponent gauge. -/
@[expose]
noncomputable def schattenFamily (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ) (hp : 1 ≤ p) : OperatorIdealFamily.{u, v, w} 𝕜 :=
  symmetricGaugeFamily 𝕜 (schattenGauge p hp)

/-- The Schatten family's gauge is the `ℓᵖ` gauge of the approximation-number
sequence. -/
theorem schattenFamily_gauge {p : ℝ} (hp : 1 ≤ p) {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (schattenFamily 𝕜 p hp).gauge A = (schattenGauge p hp).extend (approxSeq A) := rfl

/-- **The Schatten scale is antitone**, hence the ideals nest: `S_p ⊆ S_q` for
`p ≤ q`.

Entirely a transport: `schattenGaugeFun_antitone` is the `ℓ`-scale nesting at
the level of finitely supported sequences, and `extend_le_extend_of_le` carries
it to the extension, which is the family's gauge by definition. -/
theorem gauge_schattenFamily_antitone {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : p ≤ q) {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) :
    (schattenFamily 𝕜 q hq).gauge T ≤ (schattenFamily 𝕜 p hp).gauge T :=
  SymmetricGauge.extend_le_extend_of_le
    (fun c => schattenGaugeFun_antitone hp hq hpq c) (approxSeq T)


/-- The diagonal adjoint-invariant view of a finite-exponent Schatten family. -/
noncomputable def schattenFamilySymmetric (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ) (hp : 1 ≤ p) : SymmetricOperatorIdealFamily.{u, v} 𝕜 :=
  symmetricGaugeFamilySymmetric 𝕜 (schattenGauge p hp)

/-- The gauge of the Schatten family is its power-sum norm. -/
@[simp]
theorem gauge_schattenFamily {p : ℝ} (hp : 1 ≤ p) {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (schattenFamily.{u, v, w} 𝕜 p hp).gauge A = A.schattenENorm p :=
  extend_approxSeq_schattenGauge hp A

/-- The diagonal view has the same power-sum gauge. -/
@[simp]
theorem gauge_schattenFamilySymmetric {p : ℝ} (hp : 1 ≤ p) {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    (schattenFamilySymmetric.{u, v} 𝕜 p hp).gauge A = A.schattenENorm p :=
  gauge_schattenFamily hp A

/-- Membership is finiteness of the Schatten norm. -/
theorem mem_schattenFamily_carrier_iff {p : ℝ} (hp : 1 ≤ p) {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) :
    A ∈ (schattenFamily.{u, v, w} 𝕜 p hp).carrier ↔ A.IsSchattenClass p := by
  rw [OperatorIdealFamily.mem_carrier_iff, gauge_schattenFamily]
  rfl

/-- The exponent-one diagonal view is the trace-class family. -/
theorem schattenFamilySymmetric_one_eq_traceClassIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    schattenFamilySymmetric.{u, v} 𝕜 1 le_rfl = traceClassIdealFamily.{u, v} 𝕜 := by
  apply SymmetricOperatorIdealFamily.ext
  intro E F _ _ _ _ _ _ A
  rw [gauge_schattenFamilySymmetric, gauge_traceClassIdealFamily, A.schattenENorm_one]

/-- The exponent-two diagonal view is the Hilbert--Schmidt family. -/
theorem schattenFamilySymmetric_two_eq_hilbertSchmidtIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    schattenFamilySymmetric.{u, v} 𝕜 2 one_le_two = hilbertSchmidtIdealFamily.{u, v} 𝕜 := by
  apply SymmetricOperatorIdealFamily.ext
  intro E F _ _ _ _ _ _ A
  rw [gauge_schattenFamilySymmetric, hilbertSchmidtIdealFamily_gauge, A.schattenENorm_two]

/-- The infinity endpoint is the family induced by the supremum gauge. -/
noncomputable def schattenFamilyInf (𝕜 : Type u) [RCLike 𝕜] :
    OperatorIdealFamily.{u, v, w} 𝕜 := symmetricGaugeFamily 𝕜 supGauge

/-- The adjoint-invariant diagonal view of the infinity endpoint. -/
noncomputable def schattenFamilyInfSymmetric (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 := symmetricGaugeFamilySymmetric 𝕜 supGauge

/-- The infinity gauge is the supremum of the approximation-number sequence. -/
theorem gauge_schattenFamilyInf {E : Type v} {F : Type w}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) :
    (schattenFamilyInf.{u, v, w} 𝕜).gauge T = ⨆ n, approxSeq T n :=
  supGauge_extend _

/-- The infinity endpoint is exactly the operator-norm family, not a distinct ideal. -/
theorem schattenFamilyInf_eq_operatorNormIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    schattenFamilyInf.{u, v, w} 𝕜 = operatorNormIdealFamily.{u, v, w} 𝕜 := by
  apply OperatorIdealFamily.ext
  intro E F _ _ _ _ _ _ T
  change supGauge.extend (approxSeq T) = ‖T‖ₑ
  rw [supGauge_extend_of_antitone (approxSeq_antitone T), approxSeq,
    approximationNumber_index_zero, ofReal_norm]

/-- **The Schatten ideal is complete**, for the same reason the trace-class ideal is: the
gauge dominates the operator norm, so a gauge-Cauchy sequence has an operator-norm limit,
and `schattenENorm_rpow_le_liminf` then puts that limit in the ideal and gives convergence
in the gauge. -/
instance isComplete_schattenFamily {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ} (hp : 1 ≤ p) :
    (schattenFamily.{u, v, w} 𝕜 p hp).IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    have hop : CauchySeq fun n => (a n).val :=
      TauCeti.OperatorIdealFamily.Elem.cauchySeq_val ha
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hop
    have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        (L - (a n).val).schattenENorm p ≤ ENNReal.ofReal ε := by
      intro ε hε
      rw [Metric.cauchySeq_iff] at ha
      obtain ⟨N, hN⟩ := ha ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hfatou : (L - (a n).val).schattenENorm p ^ p ≤
          Filter.liminf (fun m => ((a m).val - (a n).val).schattenENorm p ^ p)
            Filter.atTop := by
        refine ContinuousLinearMap.schattenENorm_rpow_le_liminf hp0 ?_
        have hd : Filter.Tendsto (fun m => dist ((a m).val) L) Filter.atTop (nhds 0) :=
          tendsto_iff_dist_tendsto_zero.mp hL
        simpa [dist_eq_norm] using hd
      have hev : ∀ᶠ m in Filter.atTop,
          ((a m).val - (a n).val).schattenENorm p ^ p ≤ ENNReal.ofReal ε ^ p := by
        filter_upwards [Filter.eventually_ge_atTop N] with m hm
        have hd : ‖a m - a n‖ < ε := by simpa [dist_eq_norm] using hN m hm n hn
        have hgauge : ((a m).val - (a n).val).schattenENorm p ≤ ENNReal.ofReal ε := by
          have heq : (schattenFamily.{u, v, w} 𝕜 p hp).gauge (a m - a n).val
              = ((a m).val - (a n).val).schattenENorm p :=
            gauge_schattenFamily hp _
          rw [← heq, ← TauCeti.OperatorIdealFamily.Elem.enorm_eq_gauge, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hd.le
        exact ENNReal.rpow_le_rpow hgauge hp0.le
      have hle : Filter.liminf
          (fun m => ((a m).val - (a n).val).schattenENorm p ^ p) Filter.atTop
          ≤ ENNReal.ofReal ε ^ p := by
        calc Filter.liminf
              (fun m => ((a m).val - (a n).val).schattenENorm p ^ p) Filter.atTop
            ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal ε ^ p) Filter.atTop :=
              Filter.liminf_le_liminf hev
          _ = ENNReal.ofReal ε ^ p := Filter.liminf_const _
      exact (ENNReal.rpow_le_rpow_iff hp0).mp (hfatou.trans hle)
    obtain ⟨N₁, hN₁⟩ := hcauchy 1 one_pos
    have hmemL : L ∈ (schattenFamily.{u, v, w} 𝕜 p hp).carrier := by
      have hsplit : L = (L - (a N₁).val) + (a N₁).val := by abel
      rw [TauCeti.OperatorIdealFamily.mem_carrier_iff, hsplit]
      refine ne_top_of_le_ne_top ?_
        ((schattenFamily.{u, v, w} 𝕜 p hp).gauge_add_le _ _)
      refine ENNReal.add_ne_top.mpr ⟨?_, (a N₁).gauge_val_ne_top⟩
      rw [gauge_schattenFamily]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hN₁ N₁ le_rfl)
    refine ⟨TauCeti.OperatorIdealFamily.Elem.mk hmemL, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    have hgauge : ((a n).val - L).schattenENorm p ≤ ENNReal.ofReal (ε / 2) := by
      have hneg : ((a n).val - L) = -(L - (a n).val) := by abel
      rw [hneg, ContinuousLinearMap.schattenENorm_neg]
      exact hN n hn
    have hle : ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ ≤ ε / 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hgauge
      change ((schattenFamily 𝕜 p hp).gauge
        (a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL).val).toReal ≤ ε / 2
      simpa only [gauge_schattenFamily, TauCeti.OperatorIdealFamily.Elem.val_sub,
        TauCeti.OperatorIdealFamily.Elem.val_mk,
        ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ ε / 2)] using this
    calc dist (a n) (TauCeti.OperatorIdealFamily.Elem.mk hmemL)
        = ‖a n - TauCeti.OperatorIdealFamily.Elem.mk hmemL‖ := dist_eq_norm _ _
      _ ≤ ε / 2 := hle
      _ < ε := by linarith

/-- The diagonal view is complete, being the same family read on one universe. -/
instance isComplete_schattenFamilySymmetric {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ} (hp : 1 ≤ p) :
    (schattenFamilySymmetric.{u, v} 𝕜 p hp).toOperatorIdealFamily.IsComplete :=
  isComplete_schattenFamily.{u, v, v} hp

end TauCeti
