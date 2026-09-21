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
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.GuntherIdentity
import LeanPool.NashEmbedding.NashEmbedding.Torus.Perturbation.GuntherOperator
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.CoeffTransport

/-!
# Günther's identity on the momentum side

`gunther_identity` (position space, real-valued maps) is transported to coefficient
sequences: for a vector sequence `v` whose components are rapidly decaying and
`conjReflect`-fixed (so that its synthesis `vsynth v` is a smooth periodic real map),

  `-Δ̂ (∂ᵢv · ∂ⱼv) = ∂ᵢ(Lv · ∂ⱼv) + ∂ⱼ(Lv · ∂ᵢv) - 2 Lv · ∂ᵢ∂ⱼv + 2 ∑ₖ ∂ᵢ∂ₖv · ∂ⱼ∂ₖv`

where products are `seqConv`, `·` is `dotConv`, `∂ᵢ` is `vpartial i`, `L` is `vlap`, and
`Δ̂ = laplacianCoeff` (so `-Δ̂` is `L` on scalar sequences).

Consequently the polarized pieces `Fb`, `Ub` of the Günther operator satisfy
`∂ᵢv · ∂ⱼv = ∂ᵢ Fb j v v + ∂ⱼ Fb i v v + Ub i j v v`, which is the identity behind the
ansatz of Theorem B. The dictionary between real maps `ℝⁿ → ℝᴺ` and vector sequences
(`vcoeff`, `vsynth`) is set up here as well.
-/

open scoped BigOperators ContDiff
open NashEmbedding.Sobolev Matrix

noncomputable
section

namespace NashEmbedding

variable {n N : ℕ}

/-! ## Real maps ↔ vector sequences -/

/-- Componentwise rapid decay. -/
def VRapid (n N : ℕ) (v : VecSeq n N) : Prop := ∀ α, IsRapidDecay n (v α)

/-- Componentwise `conjReflect`-fixed: the coefficients of a real-valued map. -/
def VReal (v : VecSeq n N) : Prop := ∀ α, conjReflect (v α) = v α

/-- The coefficient sequences of a real map `u : ℝⁿ → ℝᴺ`. -/
def vcoeff (n : ℕ) (u : (Fin n → ℝ) → (Fin N → ℝ)) : VecSeq n N :=
  fun α => stdFourierCoeff n (fun x => ((u x α : ℝ) : ℂ))

/-- The (real) synthesis of a vector sequence. -/
def vsynth (n : ℕ) (v : VecSeq n N) : (Fin n → ℝ) → (Fin N → ℝ) :=
  fun x α => (fourierSynthesis n (v α) x).re

lemma VRapid.vmem {v : VecSeq n N} (hv : VRapid n N v) (s : ℝ) : VMem n N s v :=
  fun α => hv α s

lemma vrapid_of_vmem {v : VecSeq n N} (hv : ∀ k : ℕ, VMem n N k v) : VRapid n N v := by
  intro α s
  exact (hv ⌈s⌉₊ α).mono (Nat.le_ceil s)

/-- Coordinate partials of periodic maps are periodic (any target). -/
lemma isPeriodic2Pi_pderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : IsPeriodic2Pi f) (i : Fin n) : IsPeriodic2Pi (pderiv i f) := by
  intro x k
  have h : (fun y => f (y + periodicShift n k)) = f := funext fun y => hf y k
  change fderiv ℝ f (x + periodicShift n k) (Pi.single i 1) = fderiv ℝ f x (Pi.single i 1)
  rw [← fderiv_comp_add_right (f := f) (x := x) (periodicShift n k), h]

lemma SmoothPeriodic.pderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : SmoothPeriodic f) (i : Fin n) : SmoothPeriodic (pderiv i f) :=
  ⟨pderiv_contDiff hf.smooth i, isPeriodic2Pi_pderiv hf.periodic i⟩

lemma SmoothPeriodic.sumSqDeriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (Fin n → ℝ) → V} (hf : SmoothPeriodic f) : SmoothPeriodic (sumSqDeriv f) := by
  refine ⟨sumSqDeriv_contDiff hf.smooth, ?_⟩
  intro x k
  change (∑ a, NashEmbedding.pderiv a (NashEmbedding.pderiv a f) (x + periodicShift n k))
      = ∑ a, NashEmbedding.pderiv a (NashEmbedding.pderiv a f) x
  exact Finset.sum_congr rfl fun a _ =>
    isPeriodic2Pi_pderiv (isPeriodic2Pi_pderiv hf.periodic a) a x k

lemma SmoothPeriodic.dotProduct {u w : (Fin n → ℝ) → (Fin N → ℝ)}
    (hu : SmoothPeriodic u) (hw : SmoothPeriodic w) :
    SmoothPeriodic (fun x => u x ⬝ᵥ w x) := by
  refine ⟨contDiff_dotProduct hu.smooth hw.smooth, ?_⟩
  intro x k
  simp only [hu.periodic x k, hw.periodic x k]

/-- The complexified component `x ↦ (u x α : ℂ)` of a smooth periodic real map is smooth
periodic. -/
lemma smoothPeriodic_ofReal_comp {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u)
    (α : Fin N) : ContDiff ℝ ∞ (fun x => ((u x α : ℝ) : ℂ)) ∧
      IsPeriodic2Pi (fun x => ((u x α : ℝ) : ℂ)) := by
  constructor
  · exact Complex.ofRealCLM.contDiff.comp
      (((ContinuousLinearMap.proj α : (Fin N → ℝ) →L[ℝ] ℝ).contDiff).comp hu.smooth)
  · intro x k
    simp only [hu.periodic x k]

lemma smoothPeriodic_ofReal_scalar {f : (Fin n → ℝ) → ℝ} (hf : SmoothPeriodic f) :
    ContDiff ℝ ∞ (fun x => ((f x : ℝ) : ℂ)) ∧ IsPeriodic2Pi (fun x => ((f x : ℝ) : ℂ)) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp hf.smooth, ?_⟩
  intro x k
  simp only [hf.periodic x k]

/-- Casting to `ℂ` commutes with `pderiv` (scalar case). -/
lemma pderiv_ofReal {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    pderiv i (fun x => ((f x : ℝ) : ℂ)) = fun x => ((pderiv i f x : ℝ) : ℂ) := by
  funext x
  have hd : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have h : HasFDerivAt (fun y => ((f y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ f x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hd.hasFDerivAt
  change fderiv ℝ (fun y => ((f y : ℝ) : ℂ)) x (Pi.single i 1) = _
  rw [h.fderiv]
  rfl

/-- Casting to `ℂ` commutes with `pderiv` (component case). -/
lemma pderiv_ofReal_comp {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : ContDiff ℝ ∞ u) (i : Fin n)
    (α : Fin N) :
    pderiv i (fun x => ((u x α : ℝ) : ℂ)) = fun x => ((pderiv i u x α : ℝ) : ℂ) := by
  funext x
  have hd : DifferentiableAt ℝ u x := hu.differentiable (by simp) x
  have h : HasFDerivAt (fun y => ((u y α : ℝ) : ℂ))
      (Complex.ofRealCLM.comp
        (((ContinuousLinearMap.proj α : (Fin N → ℝ) →L[ℝ] ℝ)).comp (fderiv ℝ u x))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x
      (((ContinuousLinearMap.proj α : (Fin N → ℝ) →L[ℝ] ℝ)).hasFDerivAt.comp x hd.hasFDerivAt)
  change fderiv ℝ (fun y => ((u y α : ℝ) : ℂ)) x (Pi.single i 1) = _
  rw [h.fderiv]
  rfl

lemma vcoeff_vrapid (hn : 0 < n) {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u) :
    VRapid n N (vcoeff n u) := fun α =>
  isRapidDecay_stdFourierCoeff hn (smoothPeriodic_ofReal_comp hu α).1
      (smoothPeriodic_ofReal_comp hu α).2

lemma vcoeff_vreal {u : (Fin n → ℝ) → (Fin N → ℝ)} :
    VReal (vcoeff n u) := fun α =>
  conjReflect_stdFourierCoeff_of_real (fun x => by simp)

/-- The synthesis of a `VReal` sequence is real: `((vsynth v x α : ℝ) : ℂ) = a_check_α x`. -/
lemma ofReal_vsynth {v : VecSeq n N} (hr : VReal v) (x : Fin n → ℝ) (α : Fin N) :
    ((vsynth n v x α : ℝ) : ℂ) = fourierSynthesis n (v α) x := by
  unfold vsynth
  exact Complex.ext (by simp) (by simp [fourierSynthesis_im_eq_zero (hr α) x])

lemma vsynth_smoothPeriodic (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) :
    SmoothPeriodic (vsynth n v) := by
  constructor
  · rw [contDiff_pi]
    intro α
    exact Complex.reCLM.contDiff.comp (fourierSynthesis_contDiff hn (hv α))
  · intro x k
    funext α
    change (fourierSynthesis n (v α) (x + periodicShift n k)).re = _
    rw [fourierSynthesis_isPeriodic2Pi x k]
    rfl

lemma vcoeff_vsynth (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v) :
    vcoeff n (vsynth n v) = v := by
  funext α
  unfold vcoeff
  have : (fun x => ((vsynth n v x α : ℝ) : ℂ)) = fourierSynthesis n (v α) := by
    funext x; exact ofReal_vsynth hr x α
  rw [this]
  funext m
  exact stdFourierCoeff_fourierSynthesis_of_rapidDecay hn (hv α) m

lemma vsynth_vcoeff (hn : 0 < n) {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u) :
    vsynth n (vcoeff n u) = u := by
  funext x α
  unfold vsynth vcoeff
  rw [fourierSynthesis_stdFourierCoeff_of_smoothPeriodic hn (smoothPeriodic_ofReal_comp hu α).1
    (smoothPeriodic_ofReal_comp hu α).2 x]
  simp

/-! ## The dictionary for derivatives and dot products -/

lemma vcoeff_pderiv (hn : 0 < n) {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u)
    (i : Fin n) : vcoeff n (pderiv i u) = vpartial i (vcoeff n u) := by
  funext α
  change stdFourierCoeff n (fun x => ((pderiv i u x α : ℝ) : ℂ))
      = partialCoeff i (stdFourierCoeff n (fun x => ((u x α : ℝ) : ℂ)))
  rw [← pderiv_ofReal_comp hu.smooth i α]
  exact stdFourierCoeff_partialDeriv' hn (smoothPeriodic_ofReal_comp hu α).1
    (smoothPeriodic_ofReal_comp hu α).2 i

lemma vcoeff_sumSqDeriv (hn : 0 < n) {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u) :
    vcoeff n (sumSqDeriv u) = vlap (vcoeff n u) := by
  funext α
  have hc : ∀ k : Fin n, pderiv k (pderiv k (fun y => ((u y α : ℝ) : ℂ)))
      = fun y => ((pderiv k (pderiv k u) y α : ℝ) : ℂ) := by
    intro k
    rw [pderiv_ofReal_comp hu.smooth k α,
      pderiv_ofReal_comp (pderiv_contDiff hu.smooth k) k α]
  have h : (fun x => ((sumSqDeriv u x α : ℝ) : ℂ))
      = fun x => ∑ k, pderiv k (pderiv k (fun y => ((u y α : ℝ) : ℂ))) x := by
    funext x
    simp only [hc]
    have hsum : sumSqDeriv u x α = ∑ k, pderiv k (pderiv k u) x α := by
      change (∑ k, pderiv k (pderiv k u) x) α = _
      simp [Finset.sum_apply]
    rw [hsum]
    push_cast
    rfl
  change stdFourierCoeff n (fun x => ((sumSqDeriv u x α : ℝ) : ℂ)) = _
  rw [h]
  exact stdFourierCoeff_sumSqDeriv hn (smoothPeriodic_ofReal_comp hu α).1
    (smoothPeriodic_ofReal_comp hu α).2

/-- Coefficients of a dot product of real maps: `dotConv` of the coefficient sequences. -/
lemma stdFourierCoeff_dotProduct (hn : 0 < n) {u w : (Fin n → ℝ) → (Fin N → ℝ)}
    (hu : SmoothPeriodic u) (hw : SmoothPeriodic w) :
    stdFourierCoeff n (fun x => ((u x ⬝ᵥ w x : ℝ) : ℂ)) = dotConv (vcoeff n u) (vcoeff n w) := by
  have h : (fun x => ((u x ⬝ᵥ w x : ℝ) : ℂ))
      = fun x => ∑ α : Fin N, ((u x α : ℝ) : ℂ) * ((w x α : ℝ) : ℂ) := by
    funext x
    change ((∑ α : Fin N, u x α * w x α : ℝ) : ℂ) = _
    push_cast
    rfl
  rw [h, stdFourierCoeff_finset_sum'
    (f := fun α x => ((u x α : ℝ) : ℂ) * ((w x α : ℝ) : ℂ)) Finset.univ (fun α _ =>
      ((smoothPeriodic_ofReal_comp hu α).1.continuous.mul
        (smoothPeriodic_ofReal_comp hw α).1.continuous))]
  funext m
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [stdFourierCoeff_mul hn (smoothPeriodic_ofReal_comp hu α).1
    (smoothPeriodic_ofReal_comp hu α).2 (smoothPeriodic_ofReal_comp hw α).1
    (smoothPeriodic_ofReal_comp hw α).2]
  rfl

/-- Coefficients of `∂ᵢ` of a real scalar function. -/
lemma stdFourierCoeff_pderiv_ofReal (hn : 0 < n) {f : (Fin n → ℝ) → ℝ} (hf : SmoothPeriodic f)
    (i : Fin n) :
    stdFourierCoeff n (fun x => ((pderiv i f x : ℝ) : ℂ))
      = partialCoeff i (stdFourierCoeff n (fun x => ((f x : ℝ) : ℂ))) := by
  rw [← pderiv_ofReal hf.smooth i]
  exact stdFourierCoeff_partialDeriv' hn (smoothPeriodic_ofReal_scalar hf).1
    (smoothPeriodic_ofReal_scalar hf).2 i

/-- Coefficients of `L = ∑ₖ ∂ₖ²` of a real scalar function: `-laplacianCoeff`. -/
lemma stdFourierCoeff_sumSqDeriv_ofReal (hn : 0 < n) {f : (Fin n → ℝ) → ℝ} (hf : SmoothPeriodic f) :
    stdFourierCoeff n (fun x => ((sumSqDeriv f x : ℝ) : ℂ))
      = fun m => -laplacianCoeff (stdFourierCoeff n (fun x => ((f x : ℝ) : ℂ))) m := by
  have hc : ∀ k : Fin n, pderiv k (pderiv k (fun y => ((f y : ℝ) : ℂ)))
      = fun y => ((pderiv k (pderiv k f) y : ℝ) : ℂ) := by
    intro k
    rw [pderiv_ofReal hf.smooth k, pderiv_ofReal (pderiv_contDiff hf.smooth k) k]
  have h : (fun x => ((sumSqDeriv f x : ℝ) : ℂ))
      = fun x => ∑ k, pderiv k (pderiv k (fun y => ((f y : ℝ) : ℂ))) x := by
    funext x
    simp only [hc]
    change ((∑ k, pderiv k (pderiv k f) x : ℝ) : ℂ) = _
    push_cast
    rfl
  rw [h]
  exact stdFourierCoeff_sumSqDeriv hn (smoothPeriodic_ofReal_scalar hf).1
    (smoothPeriodic_ofReal_scalar hf).2

/-! ## The identity on sequences -/

/-- **Günther's identity on the momentum side.** -/
theorem gunther_identity_seq (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v)
    (i j : Fin n) :
    (fun m => -laplacianCoeff (dotConv (vpartial i v) (vpartial j v)) m) =
      fun m => partialCoeff i (dotConv (vlap v) (vpartial j v)) m
        + partialCoeff j (dotConv (vlap v) (vpartial i v)) m
        - 2 * dotConv (vlap v) (vpartial i (vpartial j v)) m
        + 2 * ∑ k, dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v)) m := by
  obtain ⟨V, hV, hvc⟩ : ∃ V : (Fin n → ℝ) → (Fin N → ℝ), SmoothPeriodic V ∧ vcoeff n V = v :=
    ⟨vsynth n v, vsynth_smoothPeriodic hn hv, vcoeff_vsynth hn hv hr⟩
  have hd : ∀ a, SmoothPeriodic (pderiv a V) := fun a => hV.pderiv a
  have hdd : ∀ a b, SmoothPeriodic (pderiv a (pderiv b V)) := fun a b => (hd b).pderiv a
  have hL : SmoothPeriodic (sumSqDeriv V) := hV.sumSqDeriv
  -- the position-space identity, cast to `ℂ`
  have hid : (fun x => ((sumSqDeriv (fun y => pderiv i V y ⬝ᵥ pderiv j V y) x : ℝ) : ℂ))
      = fun x => ((pderiv i (fun y => sumSqDeriv V y ⬝ᵥ pderiv j V y) x : ℝ) : ℂ)
          + ((pderiv j (fun y => sumSqDeriv V y ⬝ᵥ pderiv i V y) x : ℝ) : ℂ)
          - 2 * ((sumSqDeriv V x ⬝ᵥ pderiv i (pderiv j V) x : ℝ) : ℂ)
          + 2 * ∑ k, ((pderiv i (pderiv k V) x ⬝ᵥ pderiv j (pderiv k V) x : ℝ) : ℂ) := by
    funext x
    rw [gunther_identity hV.smooth i j]
    push_cast
    ring
  have hcoef := congrArg (stdFourierCoeff n) hid
  -- the left-hand side
  have hLHS : stdFourierCoeff n
      (fun x => ((sumSqDeriv (fun y => pderiv i V y ⬝ᵥ pderiv j V y) x : ℝ) : ℂ))
      = fun m => -laplacianCoeff (dotConv (vpartial i v) (vpartial j v)) m := by
    rw [stdFourierCoeff_sumSqDeriv_ofReal hn ((hd i).dotProduct (hd j)),
      stdFourierCoeff_dotProduct hn (hd i) (hd j), vcoeff_pderiv hn hV i,
      vcoeff_pderiv hn hV j, hvc]
  -- the four pieces of the right-hand side
  have hA : stdFourierCoeff n
      (fun x => ((pderiv i (fun y => sumSqDeriv V y ⬝ᵥ pderiv j V y) x : ℝ) : ℂ))
      = partialCoeff i (dotConv (vlap v) (vpartial j v)) := by
    rw [stdFourierCoeff_pderiv_ofReal hn (hL.dotProduct (hd j)) i,
      stdFourierCoeff_dotProduct hn hL (hd j), vcoeff_sumSqDeriv hn hV,
      vcoeff_pderiv hn hV j, hvc]
  have hB : stdFourierCoeff n
      (fun x => ((pderiv j (fun y => sumSqDeriv V y ⬝ᵥ pderiv i V y) x : ℝ) : ℂ))
      = partialCoeff j (dotConv (vlap v) (vpartial i v)) := by
    rw [stdFourierCoeff_pderiv_ofReal hn (hL.dotProduct (hd i)) j,
      stdFourierCoeff_dotProduct hn hL (hd i), vcoeff_sumSqDeriv hn hV,
      vcoeff_pderiv hn hV i, hvc]
  have hC : stdFourierCoeff n
      (fun x => ((sumSqDeriv V x ⬝ᵥ pderiv i (pderiv j V) x : ℝ) : ℂ))
      = dotConv (vlap v) (vpartial i (vpartial j v)) := by
    rw [stdFourierCoeff_dotProduct hn hL (hdd i j), vcoeff_sumSqDeriv hn hV,
      vcoeff_pderiv hn (hd j) i, vcoeff_pderiv hn hV j, hvc]
  have hD : ∀ k : Fin n, stdFourierCoeff n
      (fun x => ((pderiv i (pderiv k V) x ⬝ᵥ pderiv j (pderiv k V) x : ℝ) : ℂ))
      = dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v)) := by
    intro k
    rw [stdFourierCoeff_dotProduct hn (hdd i k) (hdd j k),
      vcoeff_pderiv hn (hd k) i, vcoeff_pderiv hn (hd k) j, vcoeff_pderiv hn hV k, hvc]
  -- continuity of the pieces
  have cA : Continuous (fun x => ((pderiv i (fun y => sumSqDeriv V y ⬝ᵥ pderiv j V y) x : ℝ) :
      ℂ)) :=
    (smoothPeriodic_ofReal_scalar ((hL.dotProduct (hd j)).pderiv i)).1.continuous
  have cB : Continuous (fun x => ((pderiv j (fun y => sumSqDeriv V y ⬝ᵥ pderiv i V y) x : ℝ) :
      ℂ)) :=
    (smoothPeriodic_ofReal_scalar ((hL.dotProduct (hd i)).pderiv j)).1.continuous
  have cC : Continuous (fun x => ((sumSqDeriv V x ⬝ᵥ pderiv i (pderiv j V) x : ℝ) : ℂ)) :=
    (smoothPeriodic_ofReal_scalar (hL.dotProduct (hdd i j))).1.continuous
  have cD : ∀ k : Fin n,
      Continuous (fun x => ((pderiv i (pderiv k V) x ⬝ᵥ pderiv j (pderiv k V) x : ℝ) : ℂ)) :=
    fun k => (smoothPeriodic_ofReal_scalar ((hdd i k).dotProduct (hdd j k))).1.continuous
  have hRHS : stdFourierCoeff n
      (fun x => ((pderiv i (fun y => sumSqDeriv V y ⬝ᵥ pderiv j V y) x : ℝ) : ℂ)
          + ((pderiv j (fun y => sumSqDeriv V y ⬝ᵥ pderiv i V y) x : ℝ) : ℂ)
          - 2 * ((sumSqDeriv V x ⬝ᵥ pderiv i (pderiv j V) x : ℝ) : ℂ)
          + 2 * ∑ k, ((pderiv i (pderiv k V) x ⬝ᵥ pderiv j (pderiv k V) x : ℝ) : ℂ))
      = fun m => partialCoeff i (dotConv (vlap v) (vpartial j v)) m
        + partialCoeff j (dotConv (vlap v) (vpartial i v)) m
        - 2 * dotConv (vlap v) (vpartial i (vpartial j v)) m
        + 2 * ∑ k, dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v)) m := by
    rw [stdFourierCoeff_add
        (f := fun x => ((pderiv i (fun y => sumSqDeriv V y ⬝ᵥ pderiv j V y) x : ℝ) : ℂ)
          + ((pderiv j (fun y => sumSqDeriv V y ⬝ᵥ pderiv i V y) x : ℝ) : ℂ)
          - 2 * ((sumSqDeriv V x ⬝ᵥ pderiv i (pderiv j V) x : ℝ) : ℂ))
        (g := fun x => 2 * ∑ k, ((pderiv i (pderiv k V) x ⬝ᵥ pderiv j (pderiv k V) x : ℝ) : ℂ))
        (((cA.add cB).sub (continuous_const.mul cC)))
        (continuous_const.mul (continuous_finsetSum _ fun k _ => cD k)),
      stdFourierCoeff_sub
        (f := fun x => ((pderiv i (fun y => sumSqDeriv V y ⬝ᵥ pderiv j V y) x : ℝ) : ℂ)
          + ((pderiv j (fun y => sumSqDeriv V y ⬝ᵥ pderiv i V y) x : ℝ) : ℂ))
        (g := fun x => 2 * ((sumSqDeriv V x ⬝ᵥ pderiv i (pderiv j V) x : ℝ) : ℂ))
        (cA.add cB) (continuous_const.mul cC),
      stdFourierCoeff_add cA cB, stdFourierCoeff_const_mul, stdFourierCoeff_const_mul,
      stdFourierCoeff_finset_sum'
        (f := fun k x => ((pderiv i (pderiv k V) x ⬝ᵥ pderiv j (pderiv k V) x : ℝ) : ℂ))
        Finset.univ (fun k _ => cD k),
      hA, hB, hC]
    funext m
    simp only [hD]
  rw [hLHS, hRHS] at hcoef
  exact hcoef

/-- The ansatz identity: `∂ᵢv · ∂ⱼv = ∂ᵢ Fb j v v + ∂ⱼ Fb i v v + Ub i j v v`. -/
theorem dotConv_eq_Fb_Ub (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v)
    (i j : Fin n) :
    dotConv (vpartial i v) (vpartial j v) =
      fun m => partialCoeff i (Fb j v v) m + partialCoeff j (Fb i v v) m + Ub i j v v m := by
  funext m
  have hgm := congrFun (gunther_identity_seq hn hv hr i j) m
  have hd : ((1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (one_add_sum_sq_pos m).ne'
  simp only [Fb, Ub, partialCoeff, resolventCoeff, laplacianCoeff, ← Finset.sum_div] at hgm ⊢
  push_cast at hgm hd ⊢
  field_simp
  linear_combination -hgm

/-- `Ub` is symmetric on the diagonal. -/
theorem Ub_symm {v : VecSeq n N} (i j : Fin n) :
    Ub i j v v = Ub j i v v := by
  have hcomm : ∀ a b : VecSeq n N, dotConv a b = dotConv b a := by
    intro a b
    funext m
    exact Finset.sum_congr rfl fun α _ => by rw [seqConv_comm]
  have hswap : vpartial i (vpartial j v) = vpartial j (vpartial i v) := by
    funext α m
    simp only [vpartial, partialCoeff]
    ring
  have h3 : ∀ k : Fin n, dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))
      = dotConv (vpartial j (vpartial k v)) (vpartial i (vpartial k v)) := fun k => hcomm _ _
  funext m
  simp only [Ub, hcomm (vpartial i v) (vpartial j v), hswap, h3]

end NashEmbedding

end
