/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevProductGevrey

@[expose] public section

/-! Same-radius operations on literal fixed-base ordered derivative blocks. -/

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap EulerGevrey
open scoped ContDiff

variable {P E F G ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype ι]

theorem block_smul_le (directions : ι → P) (q : ℕ)
    (a : ℝ) (f : P → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    block directions q (fun y => a • f y) n x ≤ |a| *block directions q f n x := by
  let L : E →L[ℝ] E := a • ContinuousLinearMap.id ℝ E
  have hL : ‖L‖ ≤ |a| := by
    apply opNorm_le_bound _ (abs_nonneg a)
    intro v
    simp only [L, smul_apply, id_apply, norm_smul, Real.norm_eq_abs, le_refl]
  exact (block_comp_clm_le directions q L f hf n x).trans
    (mul_le_mul_of_nonneg_right hL (block_nonneg directions q f n x))

theorem block_smul_gevrey (directions : ι → P) (q : ℕ)
    (a : ℝ) (f : P → E) (hf : ContDiff ℝ ∞ f)
    (R C : ℝ) (d : ℕ) (hb : ∀ n x, block directions q f n x ≤ C*majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (fun y => a • f y) n x ≤ (|a| *C)*majorant R d n :=
  (block_smul_le directions q a f hf n x).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb n x) (abs_nonneg a))

theorem block_sub_gevrey (directions : ι → P) (q : ℕ)
    (f g : P → E) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (R C D : ℝ) (d : ℕ)
    (hb : ∀ n x, block directions q f n x ≤ C*majorant R d n)
    (hc : ∀ n x, block directions q g n x ≤ D*majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (f-g) n x ≤ (C+D)*majorant R d n :=
  (block_sub_le directions q f g hf hg n x).trans
    (by simpa only [add_mul] using add_le_add (hb n x) (hc n x))

/-- The acceleration right side has the same fixed base order and external
radius as its given velocity and forcing. Only coefficient blocks enter its
explicit amplitude. -/
theorem block_acceleration_forcing_gevrey (directions : ι → P) (q : ℕ)
    (A : P → E →L[ℝ] F) (B : P → G →L[ℝ] E) (f : P → E) (v : P → G)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (Rc R CA CB Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hRcR : Rc ≤ R)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hbA : ∀ n x, coefficientBlock directions q A n x ≤ CA*majorant Rc 0 n)
    (hbB : ∀ n x, coefficientBlock directions q B n x ≤ CB*majorant Rc 0 n)
    (d : ℕ)
    (hbf : ∀ n x, block directions q f n x ≤ Cf*majorant R d n)
    (hbv : ∀ n x, block directions q v n x ≤ Cv*majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (fun y => A y (f y-(2 : ℝ) • B y (v y))) n x ≤
      (3*CA*(Cf+6*CB*Cv))*majorant R d n := by
  have hb := block_clm_apply_gevrey directions q B v hB hv
    Rc R CB Cv hRc hRcR hCB hCv hbB d hbv
  have hsb (k y) : block directions q (fun z => (2 : ℝ) • B z (v z)) k y ≤
      (6*CB*Cv)*majorant R d k := by
    have h := block_smul_gevrey directions q 2 (fun z => B z (v z)) (hB.clm_apply hv)
      R (3*CB*Cv) d hb k y
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    convert h using 1
    ring
  have hg := block_sub_gevrey directions q f (fun z => (2 : ℝ) • B z (v z)) hf
    ((hB.clm_apply hv).const_smul 2) R Cf (6*CB*Cv) d hbf hsb
  exact block_clm_apply_gevrey directions q A (fun z => f z-(2 : ℝ) • B z (v z)) hA
    (hf.sub ((hB.clm_apply hv).const_smul 2)) Rc R CA (Cf+6*CB*Cv) hRc hRcR hCA
    (by positivity) hbA d hg n x

end EulerParameterWordGevrey
