/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import LeanPool.ZetaZeros.Hilbert.Basis
public import LeanPool.ZetaZeros.Hilbert.Dimensions
public import LeanPool.ZetaZeros.Hilbert.FIdentity
public import LeanPool.ZetaZeros.Hilbert.InnerRealL2
public import LeanPool.ZetaZeros.Hilbert.Integrals
public import LeanPool.ZetaZeros.Hilbert.L2
public import LeanPool.ZetaZeros.Hilbert.Subspaces
public import LeanPool.ZetaZeros.Meta.Attr
public import LeanPool.ZetaZeros.Numeric.MontgomeryTaylor
public import LeanPool.ZetaZeros.Zeta.Basic
public import LeanPool.ZetaZeros.Zeta.OrderConj
public import LeanPool.ZetaZeros.Zeta.Defs

/-!
# Integrability and factorisation for the Bessel coefficients

The analytic ingredients `alphaCoeff_eq` needs on top of the algebraic identity `bigF_eq`.

Integrability is Hölder with `p = q = 2`: each factor is a twisted function, square-integrable by
`memLp_fz`, against a conjugated `L²` element, so the product is `L¹`. That is what licenses
splitting the finite sum under the integral.

The factorisation of the double integral needs **no** integrability: pulling a constant out of a
Bochner integral is unconditional, so a separable integrand factors by two such pulls rather than
by Fubini.
-/

@[expose] public section

namespace ZetaZeros

open MeasureTheory

variable {lam : ℝ} {eta : ℝ → ℝ}

/-- A conjugated `L²` element is still in `L²`. -/
theorem memLp_conj_coeFn (ψ : L2Interval lam) :
    MemLp (fun u => (starRingEnd ℂ) ((ψ : ℝ → ℂ) u)) 2
      (volume.restrict (Set.Ioo (-lam) lam)) := by
  have heq : (fun u => (starRingEnd ℂ) ((ψ : ℝ → ℂ) u)) = star (ψ : ℝ → ℂ) := by
    funext u
    rfl
  rw [heq]
  exact (Lp.memLp ψ).star

/-- A twisted function against a conjugated `L²` element is integrable: Hölder with `p = q = 2`. -/
theorem integrable_fz_mul_conj (h : IsAdmissible lam eta) (x : ℂ) (ψ : L2Interval lam) :
    Integrable (fun u => fz eta x u * (starRingEnd ℂ) ((ψ : ℝ → ℂ) u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
  (memLp_fz h x).integrable_mul (memLp_conj_coeFn ψ)

/-- The even part against a conjugated `L²` element is integrable. -/
theorem integrable_gz_mul_conj (h : IsAdmissible lam eta) (z : ℂ) (ψ : L2Interval lam) :
    Integrable (fun u => gz eta z u * (starRingEnd ℂ) ((ψ : ℝ → ℂ) u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
  (memLp_gz h z).integrable_mul (memLp_conj_coeFn ψ)

/-- The odd part against a conjugated `L²` element is integrable. -/
theorem integrable_hz_mul_conj (h : IsAdmissible lam eta) (z : ℂ) (ψ : L2Interval lam) :
    Integrable (fun u => hz eta z u * (starRingEnd ℂ) ((ψ : ℝ → ℂ) u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
  (memLp_hz h z).integrable_mul (memLp_conj_coeFn ψ)

/-- **The double integral of a finite sum of separable terms.** Splitting the sum under the
integral is what needs the integrability hypothesis; each term then factors as a square with none.

This is the reusable core of `alphaCoeff_eq`, applied once per family (`fz`, `gz`, `hz`). -/
theorem integral_double_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Φ : ι → ℝ → ℂ)
    (k : ℝ → ℂ) (lam : ℝ)
    (hint : ∀ i ∈ s, Integrable (fun u => Φ i u * k u)
      (volume.restrict (Set.Ioo (-lam) lam))) :
    (∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        (∑ i ∈ s, c i * Φ i u * Φ i v) * (k u * k v))
      = ∑ i ∈ s, c i * (∫ u in Set.Ioo (-lam) lam, Φ i u * k u) ^ 2 := by
  have hstep : ∀ u : ℝ,
      (∫ v in Set.Ioo (-lam) lam, (∑ i ∈ s, c i * Φ i u * Φ i v) * (k u * k v))
        = ∑ i ∈ s, c i * Φ i u * k u * ∫ v in Set.Ioo (-lam) lam, Φ i v * k v := by
    intro u
    have hfun : (fun v => (∑ i ∈ s, c i * Φ i u * Φ i v) * (k u * k v))
        = (fun v => ∑ i ∈ s, (c i * Φ i u * k u) * (Φ i v * k v)) := by
      funext v
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hfun, MeasureTheory.integral_finsetSum _ fun i hi => (hint i hi).const_mul _]
    exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
  rw [setIntegral_congr_fun measurableSet_Ioo fun u _ => hstep u]
  have hfun2 : (fun x => ∑ i ∈ s, c i * Φ i x * k x * ∫ v in Set.Ioo (-lam) lam, Φ i v * k v)
      = (fun x => ∑ i ∈ s,
          (c i * ∫ v in Set.Ioo (-lam) lam, Φ i v * k v) * (Φ i x * k x)) := by
    funext x
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun2, MeasureTheory.integral_finsetSum _ fun i hi => (hint i hi).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul, sq]
  ring

variable {Z : Finset ℂ} {m : ℂ → ℕ}

/-- **The integral of `Φ * conj Ψ` is the `L²` inner product `⟪Ψ, Φ⟫`.** -/
theorem integral_mul_conj_eq_inner (Φ Ψ : L2Interval lam) :
    (∫ u in Set.Ioo (-lam) lam, (Φ : ℝ → ℂ) u * (starRingEnd ℂ) ((Ψ : ℝ → ℂ) u))
      = inner ℂ Ψ Φ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (.of_forall fun u => ?_)
  simp only [RCLike.inner_apply]

/-- **The Bessel coefficient in terms of one-variable integrals.**

Stated for an arbitrary family `psi`: the identity is linearity together with `bigF_eq`, so the
source's adapted-orthonormal-basis hypothesis plays no role and is dropped. -/
@[zz_tag "lem_alpha_expansion"]
theorem alphaCoeff_eq (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m)
    (psi : ℕ → L2Interval lam) (j : ℕ) :
    alphaCoeff eta lam Z m psi j
      = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
          (m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
            fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2)
        + ∑ z ∈ nonRealPart Z, (m z : ℂ) *
            ((∫ u in Set.Ioo (-lam) lam,
                gz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2
              - (∫ u in Set.Ioo (-lam) lam,
                  hz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2) := by
  classical
  set c : ℂ ⊕ ℂ ⊕ ℂ → ℂ :=
    Sum.elim (fun x => (m x : ℂ)) (Sum.elim (fun z => (m z : ℂ)) fun z => -(m z : ℂ)) with hc
  set Phi : ℂ ⊕ ℂ ⊕ ℂ → ℝ → ℂ :=
    Sum.elim (fun x => fz eta x) (Sum.elim (fun z => gz eta z) fun z => hz eta z) with hPhi
  set S : Finset (ℂ ⊕ ℂ ⊕ ℂ) :=
    (simpleRealPart Z m ∪ multipleRealPart Z m).disjSum
      ((nonRealPart Z).disjSum (nonRealPart Z)) with hS
  have hint : ∀ i ∈ S, Integrable (fun u => Phi i u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u))
      (volume.restrict (Set.Ioo (-lam) lam)) := by
    rintro (x | z | z) -
    · exact integrable_fz_mul_conj h x (psi j)
    · exact integrable_gz_mul_conj h z (psi j)
    · exact integrable_hz_mul_conj h z (psi j)
  have hkernel : ∀ u v : ℝ,
      bigF eta Z m u v * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u * (psi j : ℝ → ℂ) v)
        = (∑ i ∈ S, c i * Phi i u * Phi i v)
          * ((starRingEnd ℂ) ((psi j : ℝ → ℂ) u)
              * (starRingEnd ℂ) ((psi j : ℝ → ℂ) v)) := by
    intro u v
    have hB : ∑ z ∈ nonRealPart Z,
          (m z : ℂ) * (gz eta z u * gz eta z v - hz eta z u * hz eta z v)
        = (∑ z ∈ nonRealPart Z, (m z : ℂ) * gz eta z u * gz eta z v)
          + ∑ z ∈ nonRealPart Z, -(m z : ℂ) * hz eta z u * hz eta z v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [bigF_eq hZ, map_mul, hB, hS, Finset.sum_disjSum, Finset.sum_disjSum]
    simp only [hc, hPhi, Sum.elim_inl, Sum.elim_inr]
  calc alphaCoeff eta lam Z m psi j
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          (∑ i ∈ S, c i * Phi i u * Phi i v)
            * ((starRingEnd ℂ) ((psi j : ℝ → ℂ) u)
                * (starRingEnd ℂ) ((psi j : ℝ → ℂ) v)) := by
        simp only [alphaCoeff, alphaOf, hkernel]
    _ = ∑ i ∈ S, c i * (∫ u in Set.Ioo (-lam) lam,
          Phi i u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2 :=
        integral_double_finsetSum S c Phi
          (fun u => (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) lam hint
    _ = _ := by
        rw [hS, Finset.sum_disjSum, Finset.sum_disjSum]
        simp only [hc, hPhi, Sum.elim_inl, Sum.elim_inr]
        rw [← Finset.sum_add_distrib]
        refine congrArg (_ + ·) (Finset.sum_congr rfl fun z _ => by ring)

/-- `alphaCoeff` is `alphaOf` at the indexed member: the family parameter is spurious. -/
theorem alphaCoeff_eq_alphaOf (psi : ℕ → L2Interval lam) (j : ℕ) :
    alphaCoeff eta lam Z m psi j = alphaOf eta lam Z m (psi j) :=
  rfl

/-- **The set-integral form of `inner_symmetric_im_eq_zero`.** The pairing of two symmetric
functions over the symmetric interval is real. -/
theorem integral_symmetric_im_eq_zero {Φ₁ Φ₂ : ℝ → ℂ} (h1 : IsSymmetric Φ₁) (h2 : IsSymmetric Φ₂)
    (lam : ℝ) :
    (∫ u in Set.Ioo (-lam) lam, Φ₁ u * (starRingEnd ℂ) (Φ₂ u)).im = 0 := by
  refine Complex.conj_eq_iff_im.mp ?_
  rw [← integral_conj]
  have hpt : ∀ u : ℝ, (starRingEnd ℂ) (Φ₁ u * (starRingEnd ℂ) (Φ₂ u))
      = Φ₁ (-u) * (starRingEnd ℂ) (Φ₂ (-u)) := by
    intro u
    rw [map_mul, Complex.conj_conj, h1 u]
    congr 1
    rw [h2 (-u), neg_neg]
  calc ∫ u in Set.Ioo (-lam) lam, (starRingEnd ℂ) (Φ₁ u * (starRingEnd ℂ) (Φ₂ u))
      = ∫ u in Set.Ioo (-lam) lam, Φ₁ (-u) * (starRingEnd ℂ) (Φ₂ (-u)) :=
        integral_congr_ae (.of_forall hpt)
    _ = ∫ u in Set.Ioo (-lam) lam, Φ₁ u * (starRingEnd ℂ) (Φ₂ u) :=
        integral_comp_neg_Ioo (fun v => Φ₁ v * (starRingEnd ℂ) (Φ₂ v)) lam

/-- **The Bessel coefficients are real.** -/
@[zz_tag "lem_alpha_real"]
theorem alphaCoeff_im_eq_zero (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m)
    (psi : ℕ → L2Interval lam) (j : ℕ) (hpsi : IsSymmetric ((psi j : ℝ → ℂ))) :
    (alphaCoeff eta lam Z m psi j).im = 0 := by
  classical
  rw [alphaCoeff_eq h hZ psi j, Complex.add_im, Complex.im_sum, Complex.im_sum]
  have hreal : ∀ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m, x.im = 0 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ((Finset.mem_filter.mp hx).2).1
    · exact ((Finset.mem_filter.mp hx).2).1
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro z _
    have hg := integral_symmetric_im_eq_zero (isSymmetric_gz h z) hpsi lam
    have hh := integral_symmetric_im_eq_zero (isSymmetric_hz h z) hpsi lam
    simp [Complex.mul_im, Complex.sub_im, sq, hg, hh]
  · intro x hx
    have hf := integral_symmetric_im_eq_zero (isSymmetric_fz h (hreal x hx)) hpsi lam
    simp [Complex.mul_im, sq, hf]

/-- Orthogonality to a spanning set extends to the span. -/
theorem inner_eq_zero_of_mem_span {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {s : Set E} {v w : E} (hv : ∀ y ∈ s, inner ℂ v y = 0) (hw : w ∈ Submodule.span ℂ s) :
    inner ℂ v w = 0 := by
  induction hw using Submodule.span_induction with
  | mem y hy => exact hv y hy
  | zero => exact inner_zero_right v
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- `fzL2` agrees a.e. with `fz`. -/
theorem coeFn_fzL2 (h : IsAdmissible lam eta) (z : ℂ) :
    (fzL2 h z : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] fz eta z :=
  MemLp.coeFn_toLp (memLp_fz h z)

/-- `gzL2` agrees a.e. with `gz`. -/
theorem coeFn_gzL2 (h : IsAdmissible lam eta) (z : ℂ) :
    (gzL2 h z : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] gz eta z :=
  MemLp.coeFn_toLp (memLp_gz h z)

/-- `hzL2` agrees a.e. with `hz`. -/
theorem coeFn_hzL2 (h : IsAdmissible lam eta) (z : ℂ) :
    (hzL2 h z : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] hz eta z :=
  MemLp.coeFn_toLp (memLp_hz h z)

/-- Pointwise symmetry of a representing function gives a.e. symmetry of the `L²` element. -/
theorem isSymmetricL2_of_isSymmetric {F : L2Interval lam} {phi : ℝ → ℂ}
    (hF : (F : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] phi)
    (hphi : IsSymmetric phi) : IsSymmetricL2 F := by
  filter_upwards [hF, ae_restrict_Ioo_neg hF] with u h1 h2
  rw [h1, h2, hphi u]

/-- At a real point the twisted function is a symmetric `L²` element. -/
theorem fzL2_mem_symmetricSubspace (h : IsAdmissible lam eta) {x : ℂ} (hx : x.im = 0) :
    fzL2 h x ∈ symmetricSubspace lam :=
  isSymmetricL2_of_isSymmetric (coeFn_fzL2 h x) (isSymmetric_fz h hx)

/-- The even part is a symmetric `L²` element. -/
theorem gzL2_mem_symmetricSubspace (h : IsAdmissible lam eta) (z : ℂ) :
    gzL2 h z ∈ symmetricSubspace lam :=
  isSymmetricL2_of_isSymmetric (coeFn_gzL2 h z) (isSymmetric_gz h z)

/-- The odd part is a symmetric `L²` element. -/
theorem hzL2_mem_symmetricSubspace (h : IsAdmissible lam eta) (z : ℂ) :
    hzL2 h z ∈ symmetricSubspace lam :=
  isSymmetricL2_of_isSymmetric (coeFn_hzL2 h z) (isSymmetric_hz h z)

/-- Inner products of symmetric `L²` elements are real. -/
theorem inner_symmetricL2_im_eq_zero {F G : L2Interval lam}
    (hF : IsSymmetricL2 F) (hG : IsSymmetricL2 G) :
    (inner ℂ F G : ℂ).im = 0 := by
  refine Complex.conj_eq_iff_im.mp ?_
  rw [MeasureTheory.L2.inner_def, ← integral_conj]
  calc ∫ u in Set.Ioo (-lam) lam,
        (starRingEnd ℂ) (inner ℂ ((F : ℝ → ℂ) u) ((G : ℝ → ℂ) u))
      = ∫ u in Set.Ioo (-lam) lam, (F : ℝ → ℂ) u * (starRingEnd ℂ) ((G : ℝ → ℂ) u) := by
        refine integral_congr_ae (.of_forall fun u => ?_)
        simp only [RCLike.inner_apply, map_mul, Complex.conj_conj]
        ring
    _ = ∫ u in Set.Ioo (-lam) lam, (F : ℝ → ℂ) u * (G : ℝ → ℂ) (-u) := by
        refine integral_congr_ae ?_
        filter_upwards [hG] with u hu
        rw [hu]
    _ = ∫ u in Set.Ioo (-lam) lam, (F : ℝ → ℂ) (-u) * (G : ℝ → ℂ) u := by
        have h := integral_comp_neg_Ioo
          (fun v => (F : ℝ → ℂ) v * (G : ℝ → ℂ) (-v)) lam
        simp only [neg_neg] at h
        exact h.symm
    _ = ∫ u in Set.Ioo (-lam) lam, inner ℂ ((F : ℝ → ℂ) u) ((G : ℝ → ℂ) u) := by
        refine integral_congr_ae ?_
        filter_upwards [hF] with u hu
        simp only [RCLike.inner_apply, ← hu]
        ring

/-- The integral of `Φ * conj ψ`, for a function `Φ` agreeing a.e. with an `L²` element, is the
inner product `⟪ψ, Φ⟫`. -/
theorem integral_mul_conj_eq_inner_of_ae {Φ : ℝ → ℂ} {F : L2Interval lam}
    (hF : (F : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo (-lam) lam)] Φ) (ψ : L2Interval lam) :
    (∫ u in Set.Ioo (-lam) lam, Φ u * (starRingEnd ℂ) ((ψ : ℝ → ℂ) u)) = inner ℂ ψ F := by
  rw [← integral_mul_conj_eq_inner F ψ]
  refine integral_congr_ae ?_
  filter_upwards [hF] with u hu
  rw [hu]

/-- `alphaCoeff_eq`, restated for a single vector. Definitionally the same statement. -/
theorem alphaOf_eq (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) (φ : L2Interval lam) :
    alphaOf eta lam Z m φ
      = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
          (m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
            fz eta x u * (starRingEnd ℂ) ((φ : ℝ → ℂ) u)) ^ 2)
        + ∑ z ∈ nonRealPart Z, (m z : ℂ) *
            ((∫ u in Set.Ioo (-lam) lam,
                gz eta z u * (starRingEnd ℂ) ((φ : ℝ → ℂ) u)) ^ 2
              - (∫ u in Set.Ioo (-lam) lam,
                  hz eta z u * (starRingEnd ℂ) ((φ : ℝ → ℂ) u)) ^ 2) :=
  alphaCoeff_eq h hZ (fun _ => φ) 0

/-- A Bessel coefficient against a symmetric `L²` element is real. -/
theorem alphaOf_im_eq_zero_l2 (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) {φ : L2Interval lam}
    (hsym : IsSymmetricL2 φ) :
    (alphaOf eta lam Z m φ).im = 0 := by
  classical
  rw [alphaOf_eq h hZ, Complex.add_im, Complex.im_sum, Complex.im_sum]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro z _
    have hg : (inner ℂ φ (gzL2 h z) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (gzL2_mem_symmetricSubspace h z)
    have hh : (inner ℂ φ (hzL2 h z) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (hzL2_mem_symmetricSubspace h z)
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z),
      integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
    simp [Complex.mul_im, Complex.sub_im, sq, hg, hh]
  · intro x hx
    have hxre : x.im = 0 := by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ((Finset.mem_filter.mp hx).2).1
      · exact ((Finset.mem_filter.mp hx).2).1
    have hf : (inner ℂ φ (fzL2 h x) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (fzL2_mem_symmetricSubspace h hxre)
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
    simp [Complex.mul_im, sq, hf]

/-- **Past `dim V` the Bessel coefficient is non-positive.** -/
@[zz_tag "lem_alpha_third_nonpos"]
theorem alphaOf_re_nonpos (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hb : IsAdaptedBasis h Z m psi) {j : Fin (Module.finrank ℂ (subspaceW h Z m))}
    (hsym : IsSymmetricL2 (psi j))
    (hj : Module.finrank ℂ (subspaceV h Z m) ≤ (j : ℕ)) :
    (alphaOf eta lam Z m (psi j)).re ≤ 0 := by
  classical
  -- past `dim V`, the basis vector is orthogonal to every element of `V`
  have hV : ∀ w ∈ subspaceV h Z m, inner ℂ (psi j) w = 0 := by
    intro w hw
    rw [← hb.span_V] at hw
    refine inner_eq_zero_of_mem_span ?_ hw
    rintro y ⟨i, hi, rfl⟩
    have hlt : (i : ℕ) < Module.finrank ℂ (subspaceV h Z m) := hi
    refine hb.orthonormal.2 ?_
    intro hEq
    rw [hEq] at hj
    omega
  -- so the `fz` and `gz` pairings vanish
  have hf : ∀ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
      (∫ u in Set.Ioo (-lam) lam, fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) = 0 := by
    intro x hx
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
    exact hV _ (Submodule.subset_span (Set.mem_union_left _ ⟨x, by simpa using hx, rfl⟩))
  have hg : ∀ z ∈ nonRealPart Z,
      (∫ u in Set.Ioo (-lam) lam, gz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) = 0 := by
    intro z hz
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z)]
    exact hV _ (Submodule.subset_span (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩))
  have hA : (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
      (m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
        fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hf x hx]
    ring
  rw [alphaOf_eq h hZ, hA, zero_add, Complex.re_sum]
  -- `hzmem`, not `hz`: the odd part is called `hz`, and a hypothesis of that name shadows it
  refine Finset.sum_nonpos fun z hzmem => ?_
  rw [hg z hzmem]
  -- the surviving pairing is real, so the term is a real cast and its sign is visible
  set I := ∫ u in Set.Ioo (-lam) lam,
    hz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u) with hIdef
  have hIre : I = (I.re : ℂ) :=
    Complex.ext rfl (by
      simp only [hIdef, integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
      exact inner_symmetricL2_im_eq_zero hsym (hzL2_mem_symmetricSubspace h z))
  have hterm : (m z : ℂ) * ((0 : ℂ) ^ 2 - (I.re : ℂ) ^ 2)
      = ((-((m z : ℝ) * I.re ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hIre, hterm, Complex.ofReal_re]
  have hnn : (0 : ℝ) ≤ (m z : ℝ) * I.re ^ 2 := by positivity
  linarith

/-- The conjugate of a twisted function is still square-integrable. -/
theorem memLp_conj_fz (h : IsAdmissible lam eta) (w : ℂ) :
    MemLp (fun u => (starRingEnd ℂ) (fz eta w u)) 2
      (volume.restrict (Set.Ioo (-lam) lam)) := by
  have heq : (fun u => (starRingEnd ℂ) (fz eta w u)) = star (fz eta w) := by
    funext u
    rfl
  rw [heq]
  exact (memLp_fz h w).star

/-- **The even and odd parts differ by exactly one in squared `L²` norm** (`lem_g_h_norm_diff`).

The kernel at `0` is `1`, and by the Gram identity it is the pairing of `f_z` against
`f_{conj z}`. Pointwise the real part of that pairing is already `‖g_z‖² - ‖h_z‖²`, because the
cross term is `g conj h + h conj g = 2 re (g conj h)`, which is real, so `I` times it contributes
nothing. Taking real parts once — rather than expanding the product into four integrals and
discharging integrability for each — is what keeps this short. -/
@[zz_tag "lem_g_h_norm_diff"]
theorem integral_norm_gz_sq_sub_integral_norm_hz_sq (h : IsAdmissible lam eta) (z : ℂ) :
    (∫ u in Set.Ioo (-lam) lam, ‖gz eta z u‖ ^ 2)
      - (∫ u in Set.Ioo (-lam) lam, ‖hz eta z u‖ ^ 2) = 1 := by
  have hker : (∫ u in Set.Ioo (-lam) lam,
      fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u)) = 1 := by
    have hfac := testKernel_sub_conj h z ((starRingEnd ℂ) z)
    rw [Complex.conj_conj, sub_self] at hfac
    rw [← hfac, testKernel]
    exact h.fourier_sq_zero
  have hint : Integrable
      (fun u => fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
    (memLp_fz h z).integrable_mul (memLp_conj_fz h ((starRingEnd ℂ) z))
  have hnorm : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    intro w
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hpt : ∀ u : ℝ, ‖gz eta z u‖ ^ 2 - ‖hz eta z u‖ ^ 2
      = (fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u)).re := by
    intro u
    rw [fz_eq_gz_add_I_mul_hz eta z u, fz_eq_gz_add_I_mul_hz eta ((starRingEnd ℂ) z) u]
    simp only [gz_conj, hz_conj, hnorm, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im]
    ring
  have hgi : Integrable (fun u => ‖gz eta z u‖ ^ 2)
      (volume.restrict (Set.Ioo (-lam) lam)) :=
    (memLp_two_iff_integrable_sq_norm (memLp_gz h z).aestronglyMeasurable).mp (memLp_gz h z)
  have hhi : Integrable (fun u => ‖hz eta z u‖ ^ 2)
      (volume.restrict (Set.Ioo (-lam) lam)) :=
    (memLp_two_iff_integrable_sq_norm (memLp_hz h z).aestronglyMeasurable).mp (memLp_hz h z)
  calc (∫ u in Set.Ioo (-lam) lam, ‖gz eta z u‖ ^ 2)
        - (∫ u in Set.Ioo (-lam) lam, ‖hz eta z u‖ ^ 2)
      = ∫ u in Set.Ioo (-lam) lam, (‖gz eta z u‖ ^ 2 - ‖hz eta z u‖ ^ 2) :=
        (integral_sub hgi hhi).symm
    _ = ∫ u in Set.Ioo (-lam) lam,
          (fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u)).re :=
        integral_congr_ae (.of_forall hpt)
    _ = (∫ u in Set.Ioo (-lam) lam,
          fz eta z u * (starRingEnd ℂ) (fz eta ((starRingEnd ℂ) z) u)).re :=
        integral_re hint
    _ = 1 := by rw [hker, Complex.one_re]

/-- Conjugating the index leaves the even part unchanged as an `L²` element. -/
theorem gzL2_conj (h : IsAdmissible lam eta) (z : ℂ) :
    gzL2 h ((starRingEnd ℂ) z) = gzL2 h z := by
  simp only [gzL2, gz_conj]

/-- Membership in the non-real support, unfolded. -/
theorem mem_nonRealPart {z : ℂ} : z ∈ nonRealPart Z ↔ z ∈ Z ∧ z.im ≠ 0 :=
  Finset.mem_filter

/-- Conjugation is injective on the complex numbers. -/
theorem conj_injective : Function.Injective (starRingEnd ℂ) := by
  intro a b hab
  have h := congrArg (starRingEnd ℂ) hab
  simpa [Complex.conj_conj] using h

/-- Conjugation maps the non-real support to itself. -/
theorem conj_mem_nonRealPart (hZ : IsConjInvariant Z m) {z : ℂ}
    (hz : z ∈ nonRealPart Z) : (starRingEnd ℂ) z ∈ nonRealPart Z := by
  obtain ⟨hzZ, hzim⟩ := mem_nonRealPart.mp hz
  refine mem_nonRealPart.mpr ⟨hZ.conj_mem z hzZ, ?_⟩
  rw [Complex.conj_im]
  simpa using hzim

/-- The lower half of the non-real support is exactly the conjugate image of the upper half.
Conjugation has no fixed point there, since every point has non-zero imaginary part. -/
theorem filter_not_pos_eq_image_filter_pos (hZ : IsConjInvariant Z m) :
    ((nonRealPart Z).filter fun z => ¬ 0 < z.im)
      = ((nonRealPart Z).filter fun z => 0 < z.im).image (starRingEnd ℂ) := by
  classical
  ext w
  simp only [Finset.mem_image]
  constructor
  · intro hw
    obtain ⟨hwT, hwle⟩ := Finset.mem_filter.mp hw
    have hwim : w.im ≠ 0 := (mem_nonRealPart.mp hwT).2
    refine ⟨(starRingEnd ℂ) w, Finset.mem_filter.mpr
      ⟨conj_mem_nonRealPart hZ hwT, ?_⟩, Complex.conj_conj w⟩
    rw [Complex.conj_im]
    have hneg : w.im < 0 := lt_of_le_of_ne (not_lt.mp hwle) hwim
    linarith
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzT, hzpos⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨conj_mem_nonRealPart hZ hzT, ?_⟩
    rw [Complex.conj_im, not_lt]
    linarith

/-- The non-real support has exactly twice as many points as its upper half. -/
theorem card_nonRealPart_eq_two_mul (hZ : IsConjInvariant Z m) :
    (nonRealPart Z).card
      = 2 * ((nonRealPart Z).filter fun z => 0 < z.im).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := nonRealPart Z) (p := fun z : ℂ => 0 < z.im)
  rw [filter_not_pos_eq_image_filter_pos hZ,
    Finset.card_image_of_injective _ conj_injective] at hsplit
  omega

/-- **The dimension of `U`** (`lem_dim_U`). It is spanned by one vector per multiple real point
together with the even parts at the non-real points, and conjugation identifies those in pairs, so
they contribute only half of `|S|`. The half is exact rather than a floor, because `|S|` is even. -/
@[zz_tag "lem_dim_U"]
theorem finrank_subspaceU_le (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) :
    Module.finrank ℂ (subspaceU h Z m)
      ≤ (multipleRealPart Z m).card + (nonRealPart Z).card / 2 := by
  classical
  set P := (nonRealPart Z).filter fun z => 0 < z.im with hP
  have hTsplit : nonRealPart Z = P ∪ P.image (starRingEnd ℂ) := by
    rw [hP, ← filter_not_pos_eq_image_filter_pos hZ, Finset.filter_union_filter_not_eq]
  have himg : gzL2 h '' (nonRealPart Z : Set ℂ) = gzL2 h '' (P : Set ℂ) := by
    rw [hTsplit, Finset.coe_union, Set.image_union, Finset.coe_image, Set.image_image]
    simp only [gzL2_conj]
    rw [Set.union_self]
  have hsup : subspaceU h Z m
      = Submodule.span ℂ (fzL2 h '' (multipleRealPart Z m : Set ℂ))
        ⊔ Submodule.span ℂ (gzL2 h '' (P : Set ℂ)) := by
    rw [subspaceU, ← Submodule.span_union, himg]
  have : FiniteDimensional ℂ
      (Submodule.span ℂ (fzL2 h '' (multipleRealPart Z m : Set ℂ))) :=
    FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet _).image _)
  have : FiniteDimensional ℂ (Submodule.span ℂ (gzL2 h '' (P : Set ℂ))) :=
    FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet _).image _)
  have hle : Module.finrank ℂ (subspaceU h Z m)
      ≤ Module.finrank ℂ (Submodule.span ℂ (fzL2 h '' (multipleRealPart Z m : Set ℂ)))
        + Module.finrank ℂ (Submodule.span ℂ (gzL2 h '' (P : Set ℂ))) := by
    rw [hsup]
    exact finrank_sup_le _ _
  have hf : Module.finrank ℂ
      (Submodule.span ℂ (fzL2 h '' (multipleRealPart Z m : Set ℂ)))
      ≤ (multipleRealPart Z m).card := by
    rw [show fzL2 h '' (multipleRealPart Z m : Set ℂ)
        = (((multipleRealPart Z m).image (fzL2 h) : Finset (L2Interval lam)) : Set _) by
      rw [Finset.coe_image]]
    exact le_trans (finrank_span_finset_le_card _) Finset.card_image_le
  have hg : Module.finrank ℂ (Submodule.span ℂ (gzL2 h '' (P : Set ℂ))) ≤ P.card := by
    rw [show gzL2 h '' (P : Set ℂ)
        = ((P.image (gzL2 h) : Finset (L2Interval lam)) : Set _) by rw [Finset.coe_image]]
    exact le_trans (finrank_span_finset_le_card _) Finset.card_image_le
  have hhalf := card_nonRealPart_eq_two_mul (m := m) hZ
  -- stated after `set`, so it still mentions the filter; fold it to `P` or omega
  -- sees two unrelated quantities
  rw [← hP] at hhalf
  omega

/-!
### Alternating series, and the three external inputs
-/

/-- **Alternating series bracketing** (`lem_alt_bracket`). The partial sums of an alternating
series with antitone terms bracket its limit: even-length sums from below, odd-length from above.

Generalised off the source, which also assumes the terms non-negative and null: neither is needed
once the limit is a hypothesis, and Mathlib's two one-sided bounds ask only for antitonicity. -/
@[zz_tag "lem_alt_bracket"]
theorem alternating_series_bracket {a : ℕ → ℝ} (ha : Antitone a) {L : ℝ}
    (hL : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * a i)
      Filter.atTop (nhds L)) (n : ℕ) :
    (∑ i ∈ Finset.range (2 * n), (-1 : ℝ) ^ i * a i) ≤ L ∧
      L ≤ ∑ i ∈ Finset.range (2 * n + 1), (-1 : ℝ) ^ i * a i :=
  ⟨ha.alternating_series_le_tendsto hL n, ha.tendsto_le_alternating_series hL n⟩

/-!
### Bessel input for the second-range estimate
-/

/-- The squared `L²` norm as an integral of squared pointwise norms. -/
theorem norm_sq_eq_integral (F : L2Interval lam) :
    ‖F‖ ^ 2 = ∫ u in Set.Ioo (-lam) lam, ‖(F : ℝ → ℂ) u‖ ^ 2 := by
  have hL : (∫ u in Set.Ioo (-lam) lam,
      (F : ℝ → ℂ) u * (starRingEnd ℂ) ((F : ℝ → ℂ) u))
      = ((∫ u in Set.Ioo (-lam) lam, ‖(F : ℝ → ℂ) u‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (.of_forall fun u => ?_)
    simp only [Complex.mul_conj, ← Complex.sq_norm]
  rw [integral_mul_conj_eq_inner F F, inner_self_eq_norm_sq_to_K] at hL
  -- hL carries the cast INSIDE the square; the goal wants it outside
  have hcast : ((‖F‖ ^ 2 : ℝ) : ℂ)
      = ((∫ u in Set.Ioo (-lam) lam, ‖(F : ℝ → ℂ) u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact hL
  exact Complex.ofReal_inj.mp hcast

/-- At a real point the twisted function is a unit vector of `L²`. -/
theorem norm_fzL2_sq_eq_one (h : IsAdmissible lam eta) {x : ℂ} (hx : x.im = 0) :
    ‖fzL2 h x‖ ^ 2 = 1 := by
  rw [norm_sq_eq_integral]
  rw [show (∫ u in Set.Ioo (-lam) lam, ‖((fzL2 h x : L2Interval lam) : ℝ → ℂ) u‖ ^ 2)
      = ∫ u in Set.Ioo (-lam) lam, ‖fz eta x u‖ ^ 2 from
    integral_congr_ae (by filter_upwards [coeFn_fzL2 h x] with u hu; rw [hu])]
  exact integral_norm_fz_sq h hx

/-- **Orthogonality to an initial segment's span.** If the first `d` members of an orthonormal
family span `K`, then every later member is orthogonal to all of `K`.

Factored out because both range estimates need it — for `U` and for `V` — with only `d` changing. -/
theorem inner_eq_zero_of_span_initial {N : ℕ} {psi : Fin N → L2Interval lam}
    (horth : Orthonormal ℂ psi) {d : ℕ} {K : Submodule ℂ (L2Interval lam)}
    (hspan : Submodule.span ℂ (psi '' {i | (i : ℕ) < d}) = K)
    {j : Fin N} (hj : d ≤ (j : ℕ)) :
    ∀ w ∈ K, inner ℂ (psi j) w = 0 := by
  intro w hw
  rw [← hspan] at hw
  refine inner_eq_zero_of_mem_span ?_ hw
  rintro y ⟨i, hi, rfl⟩
  have hlt : (i : ℕ) < d := hi
  refine horth.2 ?_
  intro hEq
  rw [hEq] at hj
  omega

/-- `R₁` and `R₂` are disjoint: multiplicity exactly one versus at least two. -/
theorem disjoint_simpleRealPart_multipleRealPart :
    Disjoint (simpleRealPart Z m) (multipleRealPart Z m) := by
  classical
  refine Finset.disjoint_left.mpr fun x hx1 hx2 => ?_
  have h1 : m x = 1 := ((Finset.mem_filter.mp hx1).2).2
  have h2 : 2 ≤ m x := ((Finset.mem_filter.mp hx2).2).2
  omega

/-- **The second-range estimate** (`lem_alpha_second_upper`). Summed over `dim U < j ≤ dim V`, the
Bessel coefficients are bounded by the number of simple real points.

Past `dim U` the basis vector is orthogonal to `U`, so the `R₂` and `S` pairings drop out and only
`R₁` survives — with weight one, since that is what `R₁` means. Discarding the subtracted `h_z` sum
(non-negative) and applying Bessel to each `f_x`, which is a unit vector at a real point, gives one
per point of `R₁`. -/
@[zz_tag "lem_alpha_second_upper"]
theorem sum_alphaOf_re_le_card_simpleRealPart (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hb : IsAdaptedBasis h Z m psi) (hsym : ∀ j, IsSymmetricL2 (psi j)) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
        Module.finrank ℂ (subspaceU h Z m) ≤ (j : ℕ) ∧
          (j : ℕ) < Module.finrank ℂ (subspaceV h Z m)),
      (alphaOf eta lam Z m (psi j)).re
      ≤ (simpleRealPart Z m).card := by
  classical
  set s := Finset.univ.filter (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
    Module.finrank ℂ (subspaceU h Z m) ≤ (j : ℕ) ∧
      (j : ℕ) < Module.finrank ℂ (subspaceV h Z m)) with hs
  have hstep : ∀ j : Fin (Module.finrank ℂ (subspaceW h Z m)),
      Module.finrank ℂ (subspaceU h Z m) ≤ (j : ℕ) →
      (alphaOf eta lam Z m (psi j)).re
        ≤ ∑ x ∈ simpleRealPart Z m, ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 := by
    intro j hj
    have hU := inner_eq_zero_of_span_initial hb.orthonormal hb.span_U hj
    have hf2 : ∀ x ∈ multipleRealPart Z m,
        (∫ u in Set.Ioo (-lam) lam,
          fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) = 0 := by
      intro x hx
      rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
      exact hU _ (Submodule.subset_span (Set.mem_union_left _ ⟨x, by simpa using hx, rfl⟩))
    have hgz : ∀ z ∈ nonRealPart Z,
        (∫ u in Set.Ioo (-lam) lam,
          gz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) = 0 := by
      intro z hz
      rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z)]
      exact hU _ (Submodule.subset_span (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩))
    have hR1 : ∀ x ∈ simpleRealPart Z m,
        ((m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
          fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2).re
        = ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 := by
      intro x hx
      have hm : m x = 1 := ((Finset.mem_filter.mp hx).2).2
      have hxre : x.im = 0 := ((Finset.mem_filter.mp hx).2).1
      have hbridge := integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x) (psi j)
      have hIim : (inner ℂ (psi j) (fzL2 h x) : ℂ).im = 0 := by
        exact inner_symmetricL2_im_eq_zero (hsym j) (fzL2_mem_symmetricSubspace h hxre)
      -- rewrite the norm BEFORE `sq` fires, or `Complex.sq_norm` no longer matches
      rw [hm, hbridge, Complex.sq_norm, Complex.normSq_apply]
      simp only [Nat.cast_one, one_mul, sq, Complex.mul_re, hIim]
      ring
    have hR2 : ∑ x ∈ multipleRealPart Z m,
        ((m x : ℂ) * (∫ u in Set.Ioo (-lam) lam,
          fz eta x u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2).re = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [hf2 x hx]
      simp
    have hSneg : ∑ z ∈ nonRealPart Z,
        ((m z : ℂ) * ((∫ u in Set.Ioo (-lam) lam,
            gz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2
          - (∫ u in Set.Ioo (-lam) lam,
            hz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u)) ^ 2)).re ≤ 0 := by
      refine Finset.sum_nonpos fun z hzmem => ?_
      rw [hgz z hzmem]
      set I := ∫ u in Set.Ioo (-lam) lam,
        hz eta z u * (starRingEnd ℂ) ((psi j : ℝ → ℂ) u) with hIdef
      have hIre : I = (I.re : ℂ) :=
        Complex.ext rfl (by
          simp only [hIdef, integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
          exact inner_symmetricL2_im_eq_zero (hsym j) (hzL2_mem_symmetricSubspace h z))
      have hterm : (m z : ℂ) * ((0 : ℂ) ^ 2 - (I.re : ℂ) ^ 2)
          = ((-((m z : ℝ) * I.re ^ 2) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hIre, hterm, Complex.ofReal_re]
      have hnn : (0 : ℝ) ≤ (m z : ℝ) * I.re ^ 2 := by positivity
      linarith
    rw [alphaOf_eq h hZ, Complex.add_re, Complex.re_sum, Complex.re_sum,
      Finset.sum_union disjoint_simpleRealPart_multipleRealPart,
      Finset.sum_congr rfl hR1]
    linarith
  calc ∑ j ∈ s, (alphaOf eta lam Z m (psi j)).re
      ≤ ∑ j ∈ s, ∑ x ∈ simpleRealPart Z m, ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 :=
        Finset.sum_le_sum fun j hj => hstep j ((Finset.mem_filter.mp hj).2).1
    _ = ∑ x ∈ simpleRealPart Z m, ∑ j ∈ s, ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 :=
        Finset.sum_comm
    _ ≤ ∑ _x ∈ simpleRealPart Z m, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hxre : x.im = 0 := ((Finset.mem_filter.mp hx).2).1
        have hbessel := hb.orthonormal.sum_inner_products_le (s := s) (fzL2 h x)
        rw [norm_fzL2_sq_eq_one h hxre] at hbessel
        exact hbessel
    _ = (simpleRealPart Z m).card := by simp

/-!
### The cutoff normalising constant
-/

/-- The extremal test function is non-negative everywhere: positive on `[-1/2, 1/2]` and zero
off it. -/
theorem extremalTest_nonneg (x : ℝ) : 0 ≤ extremalTest x := by
  rcases le_or_gt |x| (1 / 2) with hx | hx
  · exact (extremalTest_pos hx).le
  · have hz : extremalTest x = 0 := by rw [extremalTest, ite_eq_right (not_le.mpr hx)]
    exact hz.ge

/-- **The normalising constant is positive.**

The integrand `ψ²f₀` is non-negative, and on `|x| ≤ 1/2 - δ` it equals `f₀ > 0`, a set of positive
measure. Note it is NOT positive throughout `(-1/2, 1/2)`: a cutoff may vanish between `1/2 - δ`
and `1/2`, so the argument has to go through the support rather than through positivity on the
whole interval.

`0 < δ` is genuinely needed, not decoration: with `δ` negative the shrunken interval `|x| ≤ 1/2 - δ`
would be LARGER than `[-1/2, 1/2]`, and `f₀` is only positive on the latter. -/
@[zz_tag "lem_normaliser_pos"]
theorem cutoffNormaliser_pos {delta : ℝ} (hd : 0 < delta) (hd4 : delta < 1 / 4) {psi : ℝ → ℝ}
    (hpsi : IsCutoff delta psi) : 0 < cutoffNormaliser psi := by
  have hzero : ∀ x ∉ Set.Icc (-(1/2) : ℝ) (1/2), psi x ^ 2 * extremalTest x = 0 := by
    intro x hx
    have h : 1 / 2 ≤ |x| := by
      by_contra hlt
      exact hx (Set.mem_Icc.mpr (abs_le.mp (le_of_lt (not_le.mp hlt))))
    rw [hpsi.support x h]
    ring
  have hcont : ContinuousOn (fun x => psi x ^ 2 * extremalTest x)
      (Set.Icc (-(1/2) : ℝ) (1/2)) := by
    have hG : Continuous fun x : ℝ => psi x ^ 2 *
        (Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2))) :=
      (hpsi.smooth.continuous.pow 2).mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).div_const _)
    refine hG.continuousOn.congr ?_
    intro x hx
    have hx' : |x| ≤ 1 / 2 := abs_le.mpr (Set.mem_Icc.mp hx)
    change psi x ^ 2 * extremalTest x
        = psi x ^ 2 * (Real.cos (Real.sqrt 2 * x) / (Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)))
    rw [extremalTest, ite_eq_left hx']
  have hint : MeasureTheory.IntegrableOn (fun x => psi x ^ 2 * extremalTest x)
      (Set.Icc (-(1/2) : ℝ) (1/2)) := hcont.integrableOn_Icc
  have hnonneg : (0 : ℝ → ℝ)
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (-(1/2) : ℝ) (1/2))]
      fun x => psi x ^ 2 * extremalTest x :=
    Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (extremalTest_nonneg x)
  rw [cutoffNormaliser, ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hhalf : (0 : ℝ) < 1 / 2 - delta := by linarith
  have hsub : Set.Ioo (-(1/2 - delta)) (1/2 - delta)
      ⊆ Function.support (fun x => psi x ^ 2 * extremalTest x)
        ∩ Set.Icc (-(1/2) : ℝ) (1/2) := by
    intro x hx
    have habs : |x| ≤ 1 / 2 - delta := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    have hx12 : |x| ≤ 1 / 2 := by linarith
    refine ⟨?_, Set.mem_Icc.mpr (abs_le.mp hx12)⟩
    have h1 : psi x = 1 := hpsi.eq_one x habs
    have h2 : 0 < extremalTest x := extremalTest_pos hx12
    simp only [Function.mem_support, ne_eq, h1, one_pow, one_mul]
    exact ne_of_gt h2
  have hvol : 0 < MeasureTheory.volume (Set.Ioo (-(1/2 - delta)) (1/2 - delta)) := by
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]
    linarith
  exact lt_of_lt_of_le hvol (MeasureTheory.measure_mono hsub)

/-- **Parseval at elements of the span**, for an arbitrary finite index type.

Mathlib has Bessel for an arbitrary element (`Orthonormal.sum_inner_products_le`) and the equality
only through `OrthonormalBasis`, which wants the family to span the WHOLE space. Here the family
spans a proper submodule, so the statement is proved from the expansion directly: the inner product
against a basis vector picks out that coefficient, and the squared norm is the sum of the squared
coefficients. -/
theorem sum_sq_norm_inner_eq_norm_sq_of_span {iota : Type*} [Fintype iota]
    {psi : iota → L2Interval lam}
    (horth : Orthonormal ℂ psi) {x : L2Interval lam}
    (hx : x ∈ Submodule.span ℂ (Set.range psi)) :
    ∑ j, ‖inner ℂ (psi j) x‖ ^ 2 = ‖x‖ ^ 2 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  subst hc
  -- the pairing against a family member picks out that coefficient
  simp only [horth.inner_right_fintype c]
  have hself : (inner ℂ (∑ j, c j • psi j) (∑ j, c j • psi j) : ℂ)
      = ((∑ j, ‖c j‖ ^ 2 : ℝ) : ℂ) := by
    rw [horth.inner_sum c c Finset.univ]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
  -- take REAL PARTS rather than pulling casts: the coercion in `inner_self_eq_norm_sq_to_K` is
  -- RCLike's, not `Complex.ofReal`, so `ofReal_pow` cannot match it
  have hre : RCLike.re (inner ℂ (∑ j, c j • psi j) (∑ j, c j • psi j))
      = ‖∑ j, c j • psi j‖ ^ 2 := inner_self_eq_norm_sq _
  rw [hself] at hre
  -- simp distributes the cast into the sum, putting it inside each power; fold it back
  simpa [← Complex.ofReal_pow] using hre

/-- The `Fin N` specialization of `sum_sq_norm_inner_eq_norm_sq_of_span`. -/
theorem sum_sq_norm_inner_eq_norm_sq_of_mem_span {N : ℕ} {psi : Fin N → L2Interval lam}
    (horth : Orthonormal ℂ psi) {x : L2Interval lam}
    (hx : x ∈ Submodule.span ℂ (Set.range psi)) :
    ∑ j, ‖inner ℂ (psi j) x‖ ^ 2 = ‖x‖ ^ 2 :=
  sum_sq_norm_inner_eq_norm_sq_of_span horth hx

/-- **The tensor squares pair as the square of the inner product**, hence are orthonormal in
`L²(I²)`.

This needs no Fubini: the double integral factors by pulling a constant out of each integral, the
same route `integral_double_finsetSum` takes. -/
@[zz_tag "lem_Psi_orthonormal"]
theorem integral_tensor_square_pairing {lam : ℝ} {ι : Type*} [DecidableEq ι]
    (psi : ι → Lp ℂ 2 (volume.restrict (Set.Ioo (-lam) lam)))
    (h : Orthonormal ℂ psi) (j l : ι) :
    (∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        ((psi j : ℝ → ℂ) u * (psi j : ℝ → ℂ) v) *
          (starRingEnd ℂ) ((psi l : ℝ → ℂ) u * (psi l : ℝ → ℂ) v))
      = if j = l then 1 else 0 := by
  let s : Set ℝ := Set.Ioo (-lam) lam
  let μ : Measure ℝ := volume.restrict s
  let a : ℝ → ℂ := fun x => (psi j : ℝ → ℂ) x * (starRingEnd ℂ) ((psi l : ℝ → ℂ) x)
  have ha : ∫ x, a x ∂μ = (if j = l then 1 else 0 : ℂ) := by
    have hij := (orthonormal_iff_ite.mp h) l j
    rw [MeasureTheory.L2.inner_def] at hij
    simpa [a, μ, RCLike.inner_apply', mul_comm, eq_comm] using hij
  change ∫ u, ∫ v, ((psi j : ℝ → ℂ) u * (psi j : ℝ → ℂ) v) *
          (starRingEnd ℂ) ((psi l : ℝ → ℂ) u * (psi l : ℝ → ℂ) v) ∂μ ∂μ =
      (if j = l then 1 else 0 : ℂ)
  calc
    ∫ u, ∫ v, ((psi j : ℝ → ℂ) u * (psi j : ℝ → ℂ) v) *
          (starRingEnd ℂ) ((psi l : ℝ → ℂ) u * (psi l : ℝ → ℂ) v) ∂μ ∂μ
        = ∫ u, ∫ v, a u * a v ∂μ ∂μ := by
            simp [a, mul_assoc, mul_left_comm, mul_comm]
    _ = ∫ u, a u * (∫ v, a v ∂μ) ∂μ := by
            simp [MeasureTheory.integral_const_mul]
    _ = (∫ u, a u ∂μ) * (∫ v, a v ∂μ) := by
            simp [MeasureTheory.integral_mul_const]
    _ = (if j = l then 1 else 0 : ℂ) := by
            rw [ha]
            by_cases h_eq : j = l <;> simp [h_eq]

/-!
### The total Bessel sum
-/

/-- `gzL2` has the squared norm of `gz`. -/
theorem norm_gzL2_sq (h : IsAdmissible lam eta) (z : ℂ) :
    ‖gzL2 h z‖ ^ 2 = ∫ u in Set.Ioo (-lam) lam, ‖gz eta z u‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  exact integral_congr_ae (by filter_upwards [coeFn_gzL2 h z] with u hu; rw [hu])

/-- `hzL2` has the squared norm of `hz`. -/
theorem norm_hzL2_sq (h : IsAdmissible lam eta) (z : ℂ) :
    ‖hzL2 h z‖ ^ 2 = ∫ u in Set.Ioo (-lam) lam, ‖hz eta z u‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  exact integral_congr_ae (by filter_upwards [coeFn_hzL2 h z] with u hu; rw [hu])

/-- `integral_norm_gz_sq_sub_integral_norm_hz_sq` at the level of `L²` elements. -/
theorem norm_gzL2_sq_sub_norm_hzL2_sq (h : IsAdmissible lam eta) (z : ℂ) :
    ‖gzL2 h z‖ ^ 2 - ‖hzL2 h z‖ ^ 2 = 1 := by
  rw [norm_gzL2_sq, norm_hzL2_sq]
  exact integral_norm_gz_sq_sub_integral_norm_hz_sq h z

/-- The real part of a natural multiple of the square of a real complex number.

Not `private`: a private name is mangled, so the axiom probe reports `Unknown constant` for it and
then cannot gate the file at all. -/
theorem natCast_mul_sq_re {w : ℂ} (hw : w.im = 0) (n : ℕ) :
    ((n : ℂ) * w ^ 2).re = (n : ℝ) * ‖w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sq, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, hw]
  ring

/-- **The total Bessel sum** (`lem_alpha_sum_total`). Over the whole basis the coefficients sum to
the total multiplicity.

Parseval, not Bessel: the pairings are summed over the FULL basis, so each spanning vector
contributes exactly its squared norm — one for each `f_x` at a real point, and one for each
non-real `z` by the norm defect between `g_z` and `h_z`. -/
@[zz_tag "lem_alpha_sum_total"]
theorem sum_alphaOf_re_eq_sum_mult (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hb : IsAdaptedBasis h Z m psi) (hsym : ∀ j, IsSymmetricL2 (psi j)) :
    ∑ j, (alphaOf eta lam Z m (psi j)).re = ∑ z ∈ Z, (m z : ℝ) := by
  classical
  -- every spanning vector lies in the span of the basis
  have hmemW : ∀ y ∈ (fzL2 h '' ((simpleRealPart Z m ∪ multipleRealPart Z m : Finset ℂ) : Set ℂ))
      ∪ (gzL2 h '' (nonRealPart Z : Set ℂ)) ∪ (hzL2 h '' (nonRealPart Z : Set ℂ)),
      y ∈ Submodule.span ℂ (Set.range psi) := by
    intro y hy
    rw [hb.span_W, subspaceW]
    exact Submodule.subset_span hy
  have hfz : ∀ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
      fzL2 h x ∈ Submodule.span ℂ (Set.range psi) := fun x hx =>
    hmemW _ (Set.mem_union_left _ (Set.mem_union_left _ ⟨x, by simpa using hx, rfl⟩))
  have hgz : ∀ z ∈ nonRealPart Z, gzL2 h z ∈ Submodule.span ℂ (Set.range psi) := fun z hz =>
    hmemW _ (Set.mem_union_left _ (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩))
  have hhz : ∀ z ∈ nonRealPart Z, hzL2 h z ∈ Submodule.span ℂ (Set.range psi) := fun z hz =>
    hmemW _ (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩)
  -- termwise: the real part of each summand, in terms of squared pairings
  have hterm : ∀ j,
      (alphaOf eta lam Z m (psi j)).re
        = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
            (m x : ℝ) * ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2)
          + ∑ z ∈ nonRealPart Z, (m z : ℝ) *
              (‖inner ℂ (psi j) (gzL2 h z)‖ ^ 2 - ‖inner ℂ (psi j) (hzL2 h z)‖ ^ 2) := by
    intro j
    rw [alphaOf_eq h hZ, Complex.add_re, Complex.re_sum, Complex.re_sum]
    congr 1
    · refine Finset.sum_congr rfl fun x hx => ?_
      have hxre : x.im = 0 := by
        rcases Finset.mem_union.mp hx with hx' | hx'
        · exact ((Finset.mem_filter.mp hx').2).1
        · exact ((Finset.mem_filter.mp hx').2).1
      rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
      refine natCast_mul_sq_re ?_ _
      exact inner_symmetricL2_im_eq_zero (hsym j) (fzL2_mem_symmetricSubspace h hxre)
    · refine Finset.sum_congr rfl fun z _ => ?_
      have hgim : (inner ℂ (psi j) (gzL2 h z) : ℂ).im = 0 := by
        exact inner_symmetricL2_im_eq_zero (hsym j) (gzL2_mem_symmetricSubspace h z)
      have hhim : (inner ℂ (psi j) (hzL2 h z) : ℂ).im = 0 := by
        exact inner_symmetricL2_im_eq_zero (hsym j) (hzL2_mem_symmetricSubspace h z)
      rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z),
        integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im, sq,
        Complex.natCast_re, Complex.natCast_im, hgim, hhim]
      ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := nonRealPart Z)]
  have hone : ∀ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
      ∑ j, (m x : ℝ) * ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 = (m x : ℝ) := by
    intro x hx
    have hxre : x.im = 0 := by
      rcases Finset.mem_union.mp hx with hx' | hx'
      · exact ((Finset.mem_filter.mp hx').2).1
      · exact ((Finset.mem_filter.mp hx').2).1
    rw [← Finset.mul_sum,
      sum_sq_norm_inner_eq_norm_sq_of_mem_span hb.orthonormal (hfz x hx),
      norm_fzL2_sq_eq_one h hxre, mul_one]
  have htwo : ∀ z ∈ nonRealPart Z,
      ∑ j, (m z : ℝ) *
        (‖inner ℂ (psi j) (gzL2 h z)‖ ^ 2 - ‖inner ℂ (psi j) (hzL2 h z)‖ ^ 2) = (m z : ℝ) := by
    intro z hz
    rw [← Finset.mul_sum, Finset.sum_sub_distrib,
      sum_sq_norm_inner_eq_norm_sq_of_mem_span hb.orthonormal (hgz z hz),
      sum_sq_norm_inner_eq_norm_sq_of_mem_span hb.orthonormal (hhz z hz),
      norm_gzL2_sq_sub_norm_hzL2_sq h z, mul_one]
  rw [Finset.sum_congr rfl hone, Finset.sum_congr rfl htwo,
    ← Finset.sum_union disjoint_realPart_nonRealPart, union_realPart_nonRealPart hZ]

/-!
### The adapted orthonormal basis

The new ingredient over standard Gram--Schmidt is that every vector stays in the prescribed real
subspace, which is what carries the paper's symmetry.

Scoped in a section: it opens `Set` and `Submodule`, which the rest of this file does not.
-/

section AdaptedBasis

open Module InnerProductSpace Submodule Set

/-- **(Crux, uses `hreal`.)** Every Gram-Schmidt vector of a family lying in the real subspace `S`
stays in `S`.

Argument: strong induction on `i` using the recursion
`gramSchmidt ℂ v i = v i - ∑_{k<i} (ℂ ∙ gramSchmidt ℂ v k).starProjection (v i)`
(`InnerProductSpace.gramSchmidt_def`).  Each summand is
`(ℂ ∙ g k).starProjection (v i)`; for a unit vector `u`, `(ℂ ∙ u).starProjection w = ⟪u,w⟫ • u`,
and in general the projection onto the line `ℂ ∙ (g k)` is `(⟪g k, v i⟫ / ‖g k‖²) • g k`.  By the
induction hypothesis `g k ∈ S`, and `v i ∈ S`, so by `hreal` the coefficient `⟪g k, v i⟫` is real;
dividing by the real `‖g k‖²` keeps it real.  Since `S` is an `ℝ`-submodule it is closed under real
scalar multiplication, so each summand lies in `S`, and thus `v i - (sum) = g i ∈ S`. -/
theorem gramSchmidt_mem_S
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℝ E)
    (hreal : ∀ a ∈ S, ∀ b ∈ S, (inner ℂ a b : ℂ).im = 0)
    {n : ℕ} (v : Fin n → E) (hv : ∀ i, v i ∈ S) :
    ∀ i, gramSchmidt ℂ v i ∈ S := by
  -- A real complex scalar times an S-vector stays in S.
  have smul_mem : ∀ (c : ℂ), c.im = 0 → ∀ x ∈ S, c • x ∈ S := by
    intro c hc x hx
    have : c = ((c.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [this, Complex.coe_smul]
    exact S.smul_mem c.re hx
  -- strong induction on `i.val`.
  intro i
  induction hm : i.val using Nat.strong_induction_on generalizing i with
  | _ m IH =>
    subst hm
    have IH' : ∀ k : Fin n, k < i → gramSchmidt ℂ v k ∈ S := by
      intro k hk
      exact IH k.val hk k rfl
    rw [gramSchmidt_def ℂ v i]
    apply S.sub_mem (hv i)
    apply S.sum_mem
    intro k hk
    rw [Finset.mem_Iio] at hk
    rw [Submodule.starProjection_singleton ℂ (v i)]
    apply smul_mem
    · -- the coefficient is real
      have hnum : (inner ℂ (gramSchmidt ℂ v k) (v i) : ℂ).im = 0 :=
        hreal _ (IH' k hk) _ (hv i)
      have hden : ((‖gramSchmidt ℂ v k‖ : ℂ) ^ 2).im = 0 := by
        simp [pow_two, Complex.mul_im]
      simp [Complex.div_im, hnum, hden]
    · exact IH' k hk

/-- The *normalized* Gram-Schmidt vectors also stay in `S`: `gn i = ‖g i‖⁻¹ • g i` is a real scalar
multiple of `g i ∈ S`. -/
theorem gramSchmidtNormed_mem_S
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℝ E)
    (hreal : ∀ a ∈ S, ∀ b ∈ S, (inner ℂ a b : ℂ).im = 0)
    {n : ℕ} (v : Fin n → E) (hv : ∀ i, v i ∈ S) :
    ∀ i, gramSchmidtNormed ℂ v i ∈ S := by
  have smul_mem : ∀ (c : ℂ), c.im = 0 → ∀ x ∈ S, c • x ∈ S := by
    intro c hc x hx
    have : c = ((c.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [this, Complex.coe_smul]
    exact S.smul_mem c.re hx
  intro i
  have hmem : gramSchmidt ℂ v i ∈ S := gramSchmidt_mem_S S hreal v hv i
  unfold gramSchmidtNormed
  apply smul_mem
  · simp
  · exact hmem

-- The number of nonzero normalized Gram-Schmidt vectors equals the rank of the family.
--
-- The nonzero `gn i` form an orthonormal family (`gramSchmidtNormed_orthonormal'`), hence linearly
-- independent, and span `span ℂ (range v)`
-- (via `span_gramSchmidtNormed_range` + `span_gramSchmidt`);
-- an orthonormal spanning set of a space of finite rank `r` has exactly `r` elements.
open Classical in
theorem card_nonzero_gramSchmidtNormed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (v : Fin n → E) :
    (Finset.univ.filter (fun i : Fin n => gramSchmidtNormed ℂ v i ≠ 0)).card
      = finrank ℂ (Submodule.span ℂ (Set.range v)) := by
  classical
  set gn : Fin n → E := gramSchmidtNormed ℂ v with hgn
  -- The nonzero normalized vectors form an orthonormal (hence linearly independent) family.
  have hon : Orthonormal ℂ (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i) :=
    gramSchmidtNormed_orthonormal' v
  have hli : LinearIndependent ℂ (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i) :=
    hon.linearIndependent
  -- The span of this family equals `span (range v)`.
  have hrange : Set.range (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i)
      = gn '' {i | gn i ≠ 0} := by
    ext x
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩; exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
  have himg : gn '' {i | gn i ≠ 0} = Set.range gn \ {0} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, rfl⟩, hi⟩
    · rintro ⟨⟨i, rfl⟩, hx⟩; exact ⟨i, hx, rfl⟩
  have hspan : Submodule.span ℂ (Set.range (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i))
      = Submodule.span ℂ (Set.range v) := by
    rw [hrange, himg, Submodule.span_sdiff_singleton_zero, hgn,
      span_gramSchmidtNormed_range, span_gramSchmidt]
  -- Count via `finrank_span_eq_card`.
  rw [← hspan]
  rw [finrank_span_eq_card hli]
  -- `Fintype.card {i // gn i ≠ 0} = card of filter`.
  rw [Fintype.card_subtype]

open Classical in
private theorem span_ordered_gramSchmidtNormed_initial
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {n : ℕ} (v g gn : Fin n → E)
    (hg : g = gramSchmidt ℂ v) (hgn : gn = gramSchmidtNormed ℂ v)
    (s : Finset (Fin n)) (hs : s = Finset.univ.filter fun i => gn i ≠ 0)
    (r : ℕ) (e : Fin r → Fin n)
    (e_mem : ∀ j, e j ∈ s) (e_inj : Function.Injective e)
    (e_range : Set.range e = (s : Set (Fin n)))
    (e_lt : ∀ x y, e x < e y ↔ x < y) (e_le : ∀ x y, e x ≤ e y ↔ x ≤ y)
    (d0 : ℕ) (hd0 : d0 ≤ n) :
    Submodule.span ℂ ((fun j => gn (e j)) ''
        {j : Fin r |
          (j : ℕ) < finrank ℂ (Submodule.span ℂ (v '' {i : Fin n | (i : ℕ) < d0}))}) =
      Submodule.span ℂ (v '' {i : Fin n | (i : ℕ) < d0}) := by
  classical
  have hspanA : Submodule.span ℂ (g '' {i : Fin n | (i : ℕ) < d0}) =
      Submodule.span ℂ (v '' {i : Fin n | (i : ℕ) < d0}) := by
    rcases eq_or_lt_of_le hd0 with h | h
    · have hset : {i : Fin n | (i : ℕ) < d0} = Set.univ := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        have := i.isLt
        omega
      rw [hset, Set.image_univ, Set.image_univ, hg, span_gramSchmidt]
    · have hset : {i : Fin n | (i : ℕ) < d0} = Set.Iio (⟨d0, h⟩ : Fin n) := by
        ext i
        simp [Set.mem_Iio, Fin.lt_def]
      rw [hset, hg, span_gramSchmidt_Iio]
  set A : Set (Fin n) := {i : Fin n | (i : ℕ) < d0} with hA
  set d : ℕ := finrank ℂ (Submodule.span ℂ (v '' A)) with hd
  set T : Finset (Fin n) := s.filter (fun i => (i : ℕ) < d0) with hT
  have hcountA : T.card = d := by
    have hon : Orthonormal ℂ (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i) := by
      rw [hgn]
      exact gramSchmidtNormed_orthonormal' v
    have hTsub : ∀ i ∈ T, gn i ≠ 0 := by
      intro i hi
      rw [hT] at hi
      rw [Finset.mem_filter, hs, Finset.mem_filter] at hi
      exact hi.1.2
    set ι : {x : Fin n // x ∈ T} → {i : Fin n // gn i ≠ 0} :=
      fun x => ⟨x.1, hTsub x.1 x.2⟩ with hι
    have hιinj : Function.Injective ι := by
      intro a b hab
      apply Subtype.ext
      simpa [hι] using hab
    have honT : Orthonormal ℂ (fun x : {x : Fin n // x ∈ T} => gn x.1) := by
      exact hon.comp ι hιinj
    have hliT : LinearIndependent ℂ (fun x : {x : Fin n // x ∈ T} => gn x.1) :=
      honT.linearIndependent
    have hrangeT : Set.range (fun x : {x : Fin n // x ∈ T} => gn x.1) =
        gn '' (T : Set (Fin n)) := by
      ext y
      constructor
      · rintro ⟨⟨i, hi⟩, rfl⟩
        exact ⟨i, hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
    have hspanT : Submodule.span ℂ (gn '' (T : Set (Fin n))) =
        Submodule.span ℂ (v '' A) := by
      have hTA : (T : Set (Fin n)) ⊆ A := by
        intro i hi
        rw [Finset.mem_coe, hT, Finset.mem_filter] at hi
        exact hi.2
      have hle : Submodule.span ℂ (gn '' (T : Set (Fin n))) ≤
          Submodule.span ℂ (gn '' A) := Submodule.span_mono (Set.image_mono hTA)
      have hge : Submodule.span ℂ (gn '' A) ≤
          Submodule.span ℂ (gn '' (T : Set (Fin n))) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, hiA, rfl⟩
        by_cases hzero : gn i = 0
        · rw [hzero]
          exact Submodule.zero_mem _
        · have hiT : i ∈ T := by
            rw [hT, Finset.mem_filter, hs, Finset.mem_filter]
            exact ⟨⟨Finset.mem_univ i, hzero⟩, hiA⟩
          exact Submodule.subset_span ⟨i, hiT, rfl⟩
      have heqAT : Submodule.span ℂ (gn '' (T : Set (Fin n))) =
          Submodule.span ℂ (gn '' A) := le_antisymm hle hge
      rw [heqAT, hgn, span_gramSchmidtNormed, ← hg, hspanA]
    calc
      T.card = Fintype.card {x : Fin n // x ∈ T} := (Fintype.card_coe T).symm
      _ = finrank ℂ (Submodule.span ℂ
          (Set.range (fun x : {x : Fin n // x ∈ T} => gn x.1))) :=
        (finrank_span_eq_card hliT).symm
      _ = finrank ℂ (Submodule.span ℂ (gn '' (T : Set (Fin n)))) := by rw [hrangeT]
      _ = finrank ℂ (Submodule.span ℂ (v '' A)) := by rw [hspanT]
      _ = d := rfl
  set P : Finset (Fin r) := Finset.univ.filter (fun k => (e k : ℕ) < d0) with hP
  have hPcard : P.card = d := by
    have himg : P.image e = T := by
      ext x
      simp only [hP, hT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨e_mem k, hk⟩
      · rintro ⟨hxs, hxd0⟩
        have hxr : x ∈ Set.range e := by
          rw [e_range]
          exact Finset.mem_coe.mpr hxs
        obtain ⟨k, rfl⟩ := hxr
        exact ⟨k, hxd0, rfl⟩
    have hcardImage := Finset.card_image_of_injective P e_inj
    rw [himg, hcountA] at hcardImage
    exact hcardImage.symm
  have echar : ∀ j : Fin r, ((j : ℕ) < d ↔ (e j : ℕ) < d0) := by
    intro j
    constructor
    · intro hjd
      by_contra hcon
      push Not at hcon
      have hsub : P ⊆ Finset.Iio j := by
        intro k hk
        rw [hP, Finset.mem_filter] at hk
        have hlt : (e k : ℕ) < (e j : ℕ) := lt_of_lt_of_le hk.2 hcon
        rw [Finset.mem_Iio]
        exact (e_lt k j).mp hlt
      have hcardle : P.card ≤ (Finset.Iio j).card := Finset.card_le_card hsub
      rw [hPcard, Fin.card_Iio] at hcardle
      omega
    · intro hej
      have hsub : Finset.Iic j ⊆ P := by
        intro k hk
        rw [Finset.mem_Iic] at hk
        rw [hP, Finset.mem_filter]
        refine ⟨Finset.mem_univ k, ?_⟩
        have hkle : e k ≤ e j := (e_le k j).mpr hk
        omega
      have hcardle : (Finset.Iic j).card ≤ P.card := Finset.card_le_card hsub
      rw [hPcard, Fin.card_Iic] at hcardle
      omega
  have hseteq : e '' {j : Fin r | (j : ℕ) < d} = (T : Set (Fin n)) := by
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hT, Finset.mem_coe, Finset.mem_filter]
      exact ⟨e_mem j, (echar j).mp hj⟩
    · intro hx
      rw [hT, Finset.mem_coe, Finset.mem_filter] at hx
      obtain ⟨hxs, hxd0⟩ := hx
      have hxr : x ∈ Set.range e := by
        rw [e_range]
        exact Finset.mem_coe.mpr hxs
      obtain ⟨j, rfl⟩ := hxr
      exact ⟨j, (echar j).mpr hxd0, rfl⟩
  have himage : (fun j => gn (e j)) '' {j : Fin r | (j : ℕ) < d} =
      gn '' (e '' {j : Fin r | (j : ℕ) < d}) := by rw [Set.image_image]
  change Submodule.span ℂ ((fun j => gn (e j)) '' {j : Fin r | (j : ℕ) < d}) =
    Submodule.span ℂ (v '' A)
  rw [himage, hseteq]
  have hTA : (T : Set (Fin n)) ⊆ A := by
    intro i hi
    rw [Finset.mem_coe, hT, Finset.mem_filter] at hi
    exact hi.2
  have hle : Submodule.span ℂ (gn '' (T : Set (Fin n))) ≤
      Submodule.span ℂ (gn '' A) := Submodule.span_mono (Set.image_mono hTA)
  have hge : Submodule.span ℂ (gn '' A) ≤ Submodule.span ℂ (gn '' (T : Set (Fin n))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hiA, rfl⟩
    by_cases hzero : gn i = 0
    · rw [hzero]
      exact Submodule.zero_mem _
    · have hiT : i ∈ T := by
        rw [hT, Finset.mem_filter, hs, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ i, hzero⟩, hiA⟩
      exact Submodule.subset_span ⟨i, hiT, rfl⟩
  have heqAT : Submodule.span ℂ (gn '' (T : Set (Fin n))) =
      Submodule.span ℂ (gn '' A) := le_antisymm hle hge
  rw [heqAT, hgn, span_gramSchmidtNormed, ← hg, hspanA]

/-- **Existence of an adapted orthonormal basis inside a real subspace.**

`v` is a finite ordered family spanning `W`; its initial segments of lengths `dU` and `dV` span two
nested subspaces. There is an orthonormal family spanning the same `W`, lying in `S`, whose own
initial segments (of the appropriate dimensions) span those same two subspaces. -/
theorem exists_adapted_orthonormal_basis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℝ E)
    (hreal : ∀ a ∈ S, ∀ b ∈ S, (inner ℂ a b : ℂ).im = 0)
    {n : ℕ} (v : Fin n → E) (hv : ∀ i, v i ∈ S)
    (dU dV : ℕ) (hUV : dU ≤ dV) (hVn : dV ≤ n) :
    ∃ psi : Fin (finrank ℂ (Submodule.span ℂ (Set.range v))) → E,
      Orthonormal ℂ psi ∧
      (∀ j, psi j ∈ S) ∧
      Submodule.span ℂ (Set.range psi) = Submodule.span ℂ (Set.range v) ∧
      Submodule.span ℂ
          (psi '' {j | (j : ℕ) < finrank ℂ (Submodule.span ℂ (v '' {i | (i : ℕ) < dU}))})
        = Submodule.span ℂ (v '' {i | (i : ℕ) < dU}) ∧
      Submodule.span ℂ
          (psi '' {j | (j : ℕ) < finrank ℂ (Submodule.span ℂ (v '' {i | (i : ℕ) < dV}))})
        = Submodule.span ℂ (v '' {i | (i : ℕ) < dV}) := by
  classical
  -- Abbreviations
  set g : Fin n → E := gramSchmidt ℂ v with hg
  set gn : Fin n → E := gramSchmidtNormed ℂ v with hgn
  -- The Finset of indices whose normalized Gram-Schmidt vector is nonzero, listed in order.
  set s : Finset (Fin n) := Finset.univ.filter (fun i => gn i ≠ 0) with hs
  -- Its cardinality is the rank `r`.
  have hcard : s.card = finrank ℂ (Submodule.span ℂ (Set.range v)) := by
    rw [hs, hgn]
    exact card_nonzero_gramSchmidtNormed v
  -- Order-preserving reindexing `Fin r → Fin n` whose image is `s`.
  set r : ℕ := finrank ℂ (Submodule.span ℂ (Set.range v)) with hr
  set e : Fin r → Fin n := ⇑(s.orderEmbOfFin hcard) with he
  have e_mem : ∀ j, e j ∈ s := fun j => Finset.orderEmbOfFin_mem s hcard j
  have e_ne : ∀ j, gn (e j) ≠ 0 := by
    intro j
    have := e_mem j
    rw [hs] at this
    simpa using this
  have e_inj : Function.Injective e := (s.orderEmbOfFin hcard).injective
  have e_range : Set.range e = (s : Set (Fin n)) := Finset.range_orderEmbOfFin s hcard
  have e_lt : ∀ (x y : Fin r), e x < e y ↔ x < y := fun x y =>
    (s.orderEmbOfFin hcard).lt_iff_lt
  have e_le : ∀ (x y : Fin r), e x ≤ e y ↔ x ≤ y := fun x y =>
    (s.orderEmbOfFin hcard).le_iff_le
  have key : ∀ d0 : ℕ, d0 ≤ n →
      Submodule.span ℂ ((fun j => gn (e j)) ''
          {j : Fin r | (j : ℕ) < finrank ℂ (Submodule.span ℂ (v '' {i : Fin n | (i : ℕ) < d0}))})
        = Submodule.span ℂ (v '' {i : Fin n | (i : ℕ) < d0}) := by
    intro d0 hd0
    exact span_ordered_gramSchmidtNormed_initial v g gn hg hgn s hs r e e_mem e_inj
      e_range e_lt e_le d0 hd0
  -- The candidate basis.
  refine ⟨fun j => gn (e j), ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) Orthonormal.
    have hon : Orthonormal ℂ (fun i : {i : Fin n // gn i ≠ 0} => gn ↑i) := by
      rw [hgn]; exact gramSchmidtNormed_orthonormal' v
    set φ : Fin r → {i : Fin n // gn i ≠ 0} := fun j => ⟨e j, e_ne j⟩ with hφ
    have hφinj : Function.Injective φ := by
      intro a b hab
      apply e_inj
      simpa [hφ] using hab
    have h := hon.comp φ hφinj
    exact h
  · -- (2) Membership in S.
    intro j
    have : gramSchmidtNormed ℂ v (e j) ∈ S := gramSchmidtNormed_mem_S S hreal v hv (e j)
    rw [hgn]
    exact this
  · -- (3) span (range psi) = span (range v).
    have hrange : Set.range (fun j => gn (e j)) = gn '' s := by
      rw [Set.range_comp' gn e, e_range]
    rw [hrange]
    have himg : gn '' (s : Set (Fin n)) = Set.range gn \ {0} := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        rw [hs] at hi; simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hi
        exact ⟨⟨i, rfl⟩, hi.2⟩
      · rintro ⟨⟨i, rfl⟩, hx⟩
        refine ⟨i, ?_, rfl⟩
        rw [hs]
        simp only [Finset.coe_filter, Set.mem_ofPred_eq]
        exact ⟨Finset.mem_univ i, hx⟩
    rw [himg, Submodule.span_sdiff_singleton_zero, hgn,
      span_gramSchmidtNormed_range, span_gramSchmidt]
  · -- (4) Initial segment at dimension of `span (v '' {i < dU})`.
    -- Let `dU' = finrank ℂ (span ℂ (v '' {i < dU}))`.  Because `e` is strictly monotone with image
    -- `s`, the values `e 0, …, e (dU'-1)` are exactly the elements of `s` that are `< dU`
    -- (there are exactly `dU'` of them: the count of nonzero `gn i` among `i < dU` equals the rank
    -- of `span (g '' {i<dU}) = span (v '' {i<dU})`).  Hence
    -- `psi '' {j | j < dU'} = gn '' {i ∈ s | i < dU} = gn '' {i | i < dU}` (adding back the zero
    -- vectors does not change the span), and `span (gn '' {i<dU}) = span (g '' {i<dU})`
    -- (`span_gramSchmidtNormed`) `= span (v '' {i<dU})` (`span_gramSchmidt_Iio`).
    exact key dU (le_trans hUV hVn)
  · -- (5) Initial segment at dimension of `span (v '' {i < dV})` — identical argument to (4) with
    -- `dV` in place of `dU`.
    exact key dV hVn

end AdaptedBasis

/-! ### A symmetric adapted basis for the three Hilbert subspaces -/

/-- Enumerating a finset through its canonical equivalence with `Fin` has precisely the
finset as its range. -/
theorem range_finset_enum {E : Type*} (s : Finset E) :
    Set.range (fun i : Fin s.card => ((s.equivFin.symm i : s) : E)) = (s : Set E) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2
  · intro hx
    exact ⟨s.equivFin ⟨x, hx⟩, by simp⟩

/-- The range of two finite families appended together is the union of their ranges. -/
theorem range_fin_append {E : Type*} {a b : ℕ} (f : Fin a → E) (g : Fin b → E) :
    Set.range (Fin.append f g) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.addCases (fun j => Or.inl ⟨j, (Fin.append_left f g j).symm⟩)
      (fun j => Or.inr ⟨j, (Fin.append_right f g j).symm⟩) i
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨Fin.castAdd b i, Fin.append_left f g i⟩
    · exact ⟨Fin.natAdd a j, Fin.append_right f g j⟩

/-- The first block in an appended finite family has the expected image. -/
theorem image_append_lt_left {E : Type*} {a b : ℕ} (f : Fin a → E) (g : Fin b → E) :
    Fin.append f g '' {i : Fin (a + b) | (i : ℕ) < a} = Set.range f := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    let j : Fin a := ⟨i, hi⟩
    have hij : i = Fin.castAdd b j := Fin.ext rfl
    exact ⟨j, by rw [hij, Fin.append_left]⟩
  · rintro ⟨j, rfl⟩
    refine ⟨Fin.castAdd b j, ?_, ?_⟩
    · exact j.isLt
    · exact Fin.append_left f g j

/-- An initial segment lying in the left block of an appended family is computed in that block. -/
theorem image_append_lt_of_le {E : Type*} {a b d : ℕ} (f : Fin a → E) (g : Fin b → E)
    (hd : d ≤ a) :
    Fin.append f g '' {i : Fin (a + b) | (i : ℕ) < d}
      = f '' {i : Fin a | (i : ℕ) < d} := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hia : (i : ℕ) < a := lt_of_lt_of_le hi hd
    let j : Fin a := ⟨i, hia⟩
    have hij : i = Fin.castAdd b j := Fin.ext rfl
    exact ⟨j, hi, by rw [hij, Fin.append_left]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.castAdd b j, hj, Fin.append_left f g j⟩

/-- **A symmetric adapted basis exists.**

Order the natural spanning vectors in three blocks: the generators of `U`, the further
generators of `V`, and the further generators of `W`.  The real Gram–Schmidt construction above
then preserves symmetry and its initial segments span exactly `U` and `V`. -/
@[zz_tag "lem_adapted_basis_exists"]
theorem exists_symmetric_adapted_basis
    (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    ∃ psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam,
      IsAdaptedBasis h Z m psi ∧ ∀ j, IsSymmetricL2 (psi j) := by
  classical
  let A : Finset (L2Interval lam) :=
    (multipleRealPart Z m).image (fzL2 h) ∪ (nonRealPart Z).image (gzL2 h)
  let B : Finset (L2Interval lam) := (simpleRealPart Z m).image (fzL2 h)
  let C : Finset (L2Interval lam) := (nonRealPart Z).image (hzL2 h)
  let enumA : Fin A.card → L2Interval lam :=
    fun i => ((A.equivFin.symm i : A) : L2Interval lam)
  let enumB : Fin B.card → L2Interval lam :=
    fun i => ((B.equivFin.symm i : B) : L2Interval lam)
  let enumC : Fin C.card → L2Interval lam :=
    fun i => ((C.equivFin.symm i : C) : L2Interval lam)
  let v : Fin (A.card + B.card + C.card) → L2Interval lam :=
    Fin.append (Fin.append enumA enumB) enumC
  have hrA : Set.range enumA = (A : Set (L2Interval lam)) := range_finset_enum A
  have hrB : Set.range enumB = (B : Set (L2Interval lam)) := range_finset_enum B
  have hrC : Set.range enumC = (C : Set (L2Interval lam)) := range_finset_enum C
  have himgA : v '' {i | (i : ℕ) < A.card} = (A : Set (L2Interval lam)) := by
    rw [show v = Fin.append (Fin.append enumA enumB) enumC from rfl,
      image_append_lt_of_le _ _ (Nat.le_add_right A.card B.card),
      image_append_lt_left, hrA]
  have himgAB : v '' {i | (i : ℕ) < A.card + B.card}
      = (A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam)) := by
    rw [show v = Fin.append (Fin.append enumA enumB) enumC from rfl,
      image_append_lt_left, range_fin_append, hrA, hrB]
  have hrange : Set.range v = (A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam)) ∪
      (C : Set (L2Interval lam)) := by
    rw [show v = Fin.append (Fin.append enumA enumB) enumC from rfl,
      range_fin_append, range_fin_append, hrA, hrB, hrC]
  have hA : Submodule.span ℂ (A : Set (L2Interval lam)) = subspaceU h Z m := by
    simp only [A, Finset.coe_union, Finset.coe_image, subspaceU]
  have hAB : Submodule.span ℂ
      ((A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam))) = subspaceV h Z m := by
    simp only [A, B, Finset.coe_union, Finset.coe_image, subspaceV]
    rw [show fzL2 h '' (multipleRealPart Z m : Set ℂ) ∪
        gzL2 h '' (nonRealPart Z : Set ℂ) ∪ fzL2 h '' (simpleRealPart Z m : Set ℂ)
      = fzL2 h '' ((simpleRealPart Z m ∪ multipleRealPart Z m : Finset ℂ) : Set ℂ) ∪
        gzL2 h '' (nonRealPart Z : Set ℂ) by
          rw [Finset.coe_union, Set.image_union]
          ac_rfl]
    rw [Finset.coe_union, Set.image_union]
  have hABC : Submodule.span ℂ
      ((A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam)) ∪
        (C : Set (L2Interval lam))) = subspaceW h Z m := by
    simp only [A, B, C, Finset.coe_union, Finset.coe_image, subspaceW]
    rw [show (fzL2 h '' (multipleRealPart Z m : Set ℂ) ∪
          gzL2 h '' (nonRealPart Z : Set ℂ)) ∪ fzL2 h '' (simpleRealPart Z m : Set ℂ) ∪
          hzL2 h '' (nonRealPart Z : Set ℂ)
      = (fzL2 h '' ((simpleRealPart Z m ∪ multipleRealPart Z m : Finset ℂ) : Set ℂ) ∪
          gzL2 h '' (nonRealPart Z : Set ℂ)) ∪ hzL2 h '' (nonRealPart Z : Set ℂ) by
          rw [Finset.coe_union, Set.image_union]
          ac_rfl]
    rw [Finset.coe_union, Set.image_union]
  have hv : ∀ i, v i ∈ symmetricSubspace lam := by
    intro i
    have hi : v i ∈ (A : Set (L2Interval lam)) ∪ (B : Set (L2Interval lam)) ∪
        (C : Set (L2Interval lam)) := by
      rw [← hrange]
      exact ⟨i, rfl⟩
    rcases hi with (hi | hi) | hi
    · simp only [A, Finset.coe_union, Finset.coe_image] at hi
      rcases hi with ⟨x, hx, hxi⟩ | ⟨z, hz, hzi⟩
      · rw [← hxi]
        exact fzL2_mem_symmetricSubspace h ((Finset.mem_filter.mp hx).2).1
      · rw [← hzi]
        exact gzL2_mem_symmetricSubspace h z
    · simp only [B, Finset.coe_image] at hi
      rcases hi with ⟨x, hx, hxi⟩
      rw [← hxi]
      exact fzL2_mem_symmetricSubspace h ((Finset.mem_filter.mp hx).2).1
    · simp only [C, Finset.coe_image] at hi
      rcases hi with ⟨z, hz, hzi⟩
      rw [← hzi]
      exact hzL2_mem_symmetricSubspace h z
  have hW : Submodule.span ℂ (Set.range v) = subspaceW h Z m := by
    rw [hrange, hABC]
  have hU : Submodule.span ℂ (v '' {i | (i : ℕ) < A.card}) = subspaceU h Z m := by
    rw [himgA, hA]
  have hV : Submodule.span ℂ (v '' {i | (i : ℕ) < A.card + B.card}) = subspaceV h Z m := by
    rw [himgAB, hAB]
  have hex :=
    exists_adapted_orthonormal_basis (symmetricSubspace lam)
      (fun a ha b hb => inner_symmetricL2_im_eq_zero ha hb) v hv
      A.card (A.card + B.card) (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  rw [hW, hU, hV] at hex
  obtain ⟨psi, horth, hsym, hspanW, hspanU, hspanV⟩ := hex
  refine ⟨psi, ?_, hsym⟩
  exact ⟨horth, hspanW, hspanU, hspanV⟩

/-!
### Multiplicity of a non-trivial zero
-/

/-- **Every non-trivial zero has multiplicity at least one** (`lem_mult_pos`).

Two things have to be ruled out, and only one of them is the obvious one. The order is not `0`
because zeta is analytic at the point and vanishes there. It is also not `⊤`: zeta is not
identically zero near the point, and the only route to that is the identity theorem on the
punctured plane, where `zeta 2 ≠ 0` supplies the contradiction. -/
@[zz_tag "lem_mult_pos"]
theorem one_le_zeroMultiplicity {T : ℝ} {rho : ℂ} (hrho : rho ∈ nontrivialZeros T) :
    1 ≤ zeroMultiplicity rho := by
  obtain ⟨hzero, -, hre1, -, -⟩ := hrho
  have hne1 : rho ≠ 1 := by
    intro hEq
    rw [hEq] at hre1
    simp at hre1
  have hanaOn : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ := by
    intro w hw
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_ne.mem_nhds hw] with v hv
    exact differentiableAt_riemannZeta hv
  have hana : AnalyticAt ℂ riemannZeta rho := hanaOn rho hne1
  have hnetop : analyticOrderAt riemannZeta rho ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro hev
    have hconn : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have hEqOn := hanaOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hne1 hev
    have h2 : riemannZeta 2 = 0 := hEqOn (by norm_num : (2 : ℂ) ≠ 1)
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num) h2
  have hne0 : analyticOrderAt riemannZeta rho ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    push Not
    exact ⟨hana, hzero⟩
  have hcast := Nat.cast_analyticOrderNatAt hnetop
  simp only [zeroMultiplicity]
  refine Nat.one_le_iff_ne_zero.mpr fun h0 => hne0 ?_
  rw [← hcast, h0]
  rfl

/-!
### The rescaled zeros carry the three counts
-/

/-- The rescaling is injective: it is affine with non-zero linear coefficient. -/
theorem rescale_injective {T : ℝ} (hT : 1 < T) : Function.Injective (rescale T) := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hc : ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  intro a b hab
  simp only [rescale] at hab
  have h1 := mul_right_cancel₀ hc hab
  have h2 := mul_left_cancel₀ Complex.I_ne_zero h1
  linear_combination h2

/-- The transported multiplicity agrees with the original at a rescaled point. -/
theorem rescaledMult_rescale {T : ℝ} (hT : 1 < T) (rho : ℂ) :
    rescaledMult T (rescale T rho) = zeroMultiplicity rho := by
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hc : ((Real.log T / (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  simp only [rescaledMult, rescale]
  congr 1
  field_simp
  ring

/-- **The rescaled zeros carry the counted total** (part of `lem_Z_T_counts`). -/
@[zz_tag "lem_Z_T_counts"]
theorem sum_rescaledMult_eq_zeroCount {T : ℝ} (hT : 1 < T) :
    ∑ z ∈ rescaledZerosFinset T, rescaledMult T z = zeroCount T := by
  classical
  rw [rescaledZerosFinset, Finset.sum_image fun a _ b _ hab => rescale_injective hT hab]
  rw [zeroCount, ← finsum_mem_coe_finset]
  rw [Set.Finite.coe_toFinset]
  exact finsum_congr fun rho => by
    by_cases hmem : rho ∈ nontrivialZeros T <;>
      simp [hmem, rescaledMult_rescale hT]

/-- **The rescaled zeros carry the distinct count** (part of `lem_Z_T_counts`). -/
@[zz_tag "lem_Z_T_counts"]
theorem card_rescaledZerosFinset_eq_distinctZeroCount {T : ℝ} (hT : 1 < T) :
    (rescaledZerosFinset T).card = distinctZeroCount T := by
  classical
  -- the zero set is only known FINITE, not a Fintype, so the Fintype-flavoured
  -- `ncard_eq_toFinset_card'` does not apply; the Finite-hypothesis form does
  rw [rescaledZerosFinset, Finset.card_image_of_injective _ (rescale_injective hT),
    distinctZeroCount, Set.ncard_eq_toFinset_card _ (nontrivialZeros_finite T)]

/-- **The rescaled zeros carry the simple-on-line count** (part of `lem_Z_T_counts`).

The third of the entity's three conjuncts. Under the bijection a rescaled point is real exactly
when the zero is on the critical line (`rescale_im_eq_zero_iff`) and has multiplicity one exactly
when the zero does. -/
@[zz_tag "lem_Z_T_counts"]
theorem card_simpleRealPart_rescaled_eq_simpleOnLineCount {T : ℝ} (hT : 1 < T) :
    (simpleRealPart (rescaledZerosFinset T) (rescaledMult T)).card = simpleOnLineCount T := by
  classical
  have hfin := nontrivialZeros_finite T
  have hsub : {rho ∈ nontrivialZeros T | rho.re = 1 / 2 ∧ zeroMultiplicity rho = 1}.Finite :=
    hfin.subset fun x hx => hx.1
  have hset : simpleRealPart (rescaledZerosFinset T) (rescaledMult T)
      = (hfin.toFinset.filter fun rho => rho.re = 1 / 2 ∧ zeroMultiplicity rho = 1).image
          (rescale T) := by
    ext w
    simp only [simpleRealPart, rescaledZerosFinset, Finset.mem_filter, Finset.mem_image,
      Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨rho, hrho, rfl⟩, him, hm⟩
      refine ⟨rho, ⟨hrho, (rescale_im_eq_zero_iff hT rho).mp him, ?_⟩, rfl⟩
      rwa [rescaledMult_rescale hT] at hm
    · rintro ⟨rho, ⟨hrho, hre, hm⟩, rfl⟩
      refine ⟨⟨rho, hrho, rfl⟩, (rescale_im_eq_zero_iff hT rho).mpr hre, ?_⟩
      rw [rescaledMult_rescale hT]
      exact hm
  rw [hset, Finset.card_image_of_injective _ (rescale_injective hT), simpleOnLineCount,
    Set.ncard_eq_toFinset_card _ hsub]
  congr 1
  ext rho
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_ofPred_eq]


/-- **Parseval over a sub-family**, at elements of that sub-family's span. -/
theorem sum_sq_norm_inner_eq_norm_sq_of_mem_span_finset {iota : Type*}
    {psi : iota → L2Interval lam} (horth : Orthonormal ℂ psi)
    (s : Finset iota) {x : L2Interval lam}
    (hx : x ∈ Submodule.span ℂ (psi '' (s : Set iota))) :
    ∑ j ∈ s, ‖inner ℂ (psi j) x‖ ^ 2 = ‖x‖ ^ 2 := by
  classical
  have hsub : Orthonormal ℂ fun i : {i // i ∈ s} => psi (i : iota) :=
    horth.comp _ Subtype.val_injective
  have hrange : Set.range (fun i : {i // i ∈ s} => psi (i : iota)) = psi '' (s : Set iota) := by
    ext y
    simp only [Set.mem_range, Set.mem_image, Finset.mem_coe, Subtype.exists]
    tauto
  rw [← Finset.sum_coe_sort s fun j => ‖inner ℂ (psi j) x‖ ^ 2]
  exact sum_sq_norm_inner_eq_norm_sq_of_span hsub (by rw [hrange]; exact hx)

/-!
## The normalised test function has total mass one
-/

variable {delta : ℝ} {psi : ℝ → ℝ}

/-- The normalised square, written out: `f_psi = psi² f₀ / A_psi`. The square roots cancel because
both `f₀` and `A_psi` are non-negative. -/
theorem cutoffTestSq_eq (hd : 0 < delta) (hd4 : delta < 1 / 4) (h : IsCutoff delta psi) (x : ℝ) :
    cutoffTestSq psi x = psi x ^ 2 * extremalTest x / cutoffNormaliser psi := by
  have hA := cutoffNormaliser_pos hd hd4 h
  simp only [cutoffTestSq, cutoffTest, Pi.pow_apply]
  rw [div_pow, mul_pow, Real.sq_sqrt (extremalTest_nonneg x), Real.sq_sqrt hA.le]

/-- **The normalised test function has total mass one** (`lem_f_psi_integral`). -/
@[zz_tag "lem_f_psi_integral"]
theorem integral_cutoffTestSq (hd : 0 < delta) (hd4 : delta < 1 / 4) (h : IsCutoff delta psi) :
    ∫ x : ℝ, cutoffTestSq psi x = 1 := by
  have hA := cutoffNormaliser_pos hd hd4 h
  rw [integral_congr_ae (.of_forall fun x => cutoffTestSq_eq hd hd4 h x),
    MeasureTheory.integral_div, ← cutoffNormaliser]
  exact div_self (ne_of_gt hA)

/-- **Its Fourier transform at zero is one** (`lem_f_psi_integral`). -/
@[zz_tag "lem_f_psi_integral"]
theorem fourierC_cutoffTestSq_zero (hd : 0 < delta) (hd4 : delta < 1 / 4)
    (h : IsCutoff delta psi) : fourierC (cutoffTestSq psi) 0 = 1 := by
  have hpt : ∀ u : ℝ, ((cutoffTestSq psi u : ℝ) : ℂ) *
      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * 0 * (u : ℂ))
        = ((cutoffTestSq psi u : ℝ) : ℂ) := by
    intro u
    simp
  rw [fourierC, integral_congr_ae (.of_forall hpt), integral_complex_ofReal,
    integral_cutoffTestSq hd hd4 h]
  norm_num

/-! ## Bessel for a kernel against tensor squares

The abstract statement: it mentions no admissible `eta`, no `bigF` and no `alphaCoeff`. What the
instantiation still needs is that `bigF` and the tensor squares are `MemLp 2` for the product
measure; the orthonormality hypothesis is discharged by `integral_tensor_square_pairing`.
-/

open MeasureTheory

/-- Bridging lemma: the `L²` inner product of two tensor-type kernels on the product measure
equals the iterated integral of `f * conj g`. -/
private lemma inner_toLp_eq_iterated (lam : ℝ) (f g : ℝ → ℝ → ℂ)
    (hf : MemLp (fun p : ℝ × ℝ => f p.1 p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))))
    (hg : MemLp (fun p : ℝ × ℝ => g p.1 p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam)))) :
    inner ℂ (hg.toLp _) (hf.toLp _)
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          f u v * (starRingEnd ℂ) (g u v) := by
  have hae : ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Set.Ioo (-lam) lam)).prod
      (volume.restrict (Set.Ioo (-lam) lam))),
      inner ℂ ((hg.toLp _ : Lp ℂ 2 _) p) ((hf.toLp _ : Lp ℂ 2 _) p)
        = f p.1 p.2 * (starRingEnd ℂ) (g p.1 p.2) := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with p hp hq
    simp [hp, hq, RCLike.inner_apply]
  have hint : Integrable (fun p : ℝ × ℝ => f p.1 p.2 * (starRingEnd ℂ) (g p.1 p.2))
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))) :=
    (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hg.toLp _) (hf.toLp _)).congr hae
  rw [MeasureTheory.L2.inner_def, integral_integral hint]
  exact integral_congr_ae hae

/-- **Bessel for a kernel paired against tensor squares.**

`phi` is a finite family whose tensor squares are orthonormal in the iterated-integral pairing
(`horth`). Then the squared pairings of the kernel `K` against them are dominated by the squared
`L²` norm of `K`. -/
theorem sum_sq_pairing_le_integral_norm_sq {lam : ℝ} {N : ℕ}
    (K : ℝ → ℝ → ℂ) (phi : Fin N → ℝ → ℂ)
    (hK : MemLp (fun p : ℝ × ℝ => K p.1 p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))))
    (hphi : ∀ j, MemLp (fun p : ℝ × ℝ => phi j p.1 * phi j p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))))
    (horth : ∀ j l : Fin N,
      (∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        (phi j u * phi j v) * (starRingEnd ℂ) (phi l u * phi l v))
        = if j = l then 1 else 0) :
    ∑ j, ‖∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          K u v * (starRingEnd ℂ) (phi j u * phi j v)‖ ^ 2
      ≤ ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam, ‖K u v‖ ^ 2 := by
  classical
  -- the orthonormal family in `L²` of the product
  have horthE : Orthonormal ℂ (fun j : Fin N =>
      (hphi j).toLp (fun p : ℝ × ℝ => phi j p.1 * phi j p.2)) := by
    rw [orthonormal_iff_ite]
    intro j l
    rw [inner_toLp_eq_iterated lam (fun u v => phi l u * phi l v)
      (fun u v => phi j u * phi j v) (hphi l) (hphi j), horth l j]
    by_cases h : j = l
    · subst h; simp
    · simp [h, Ne.symm h]
  -- Bessel's inequality in `L²`
  have hbessel := horthE.sum_inner_products_le
    (hK.toLp (fun p : ℝ × ℝ => K p.1 p.2)) (s := Finset.univ)
  -- identify the pairings
  have hpair : ∀ j : Fin N,
      inner ℂ ((hphi j).toLp (fun p : ℝ × ℝ => phi j p.1 * phi j p.2))
        (hK.toLp (fun p : ℝ × ℝ => K p.1 p.2))
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          K u v * (starRingEnd ℂ) (phi j u * phi j v) := fun j =>
    inner_toLp_eq_iterated lam K (fun u v => phi j u * phi j v) hK (hphi j)
  -- identify the squared norm
  have hnorm : ‖hK.toLp (fun p : ℝ × ℝ => K p.1 p.2)‖ ^ 2
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam, ‖K u v‖ ^ 2 := by
    have h1 := inner_toLp_eq_iterated lam K K hK hK
    have h2 : ∀ u : ℝ, (∫ v in Set.Ioo (-lam) lam, K u v * (starRingEnd ℂ) (K u v))
        = ((∫ v in Set.Ioo (-lam) lam, ‖K u v‖ ^ 2 : ℝ) : ℂ) := by
      intro u
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp [Complex.mul_conj']
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h1]
    simp only [h2]
    rw [integral_complex_ofReal]
    simp
  rw [← hnorm]
  refine le_trans (le_of_eq ?_) hbessel
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hpair j]

/-- The tensor product of two `L²` functions is `L²` for the product measure. -/
theorem memLp_tensor_two {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    {mu : Measure alpha} {nu : Measure beta}
    {f : alpha → ℂ} {g : beta → ℂ} (hf : MemLp f 2 mu) (hg : MemLp g 2 nu) :
    MemLp (fun p : alpha × beta => f p.1 * g p.2) 2 (mu.prod nu) := by
  have h1 : Integrable (fun x => ‖f x‖ ^ 2) mu := (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  have h2 : Integrable (fun y => ‖g y‖ ^ 2) nu := (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  have hmul : Integrable (fun z : alpha × beta => ‖f z.1‖ ^ 2 * ‖g z.2‖ ^ 2) (mu.prod nu) :=
    h1.mul_prod h2
  have hmeas : AEStronglyMeasurable (fun p : alpha × beta => f p.1 * g p.2) (mu.prod nu) :=
    hf.1.comp_fst.mul hg.1.comp_snd
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine hmul.congr ?_
  filter_upwards with z
  simp [mul_pow]

/-- **The normalised cutoff test function is `1/2`-admissible.**

Three of the four fields are the smoothness, support and integral facts for `cutoffTest` read off
directly. Only square-integrability is new, and it is immediate once the function is known to be
continuous with compact support -- which is why `HasCompactSupport` was worth stating there rather
than leaving the support condition purely pointwise. -/
@[zz_tag "lem_eta_psi_admissible"]
theorem isAdmissible_cutoffTest {delta : ℝ} (hd : 0 < delta) (hd4 : delta < 1 / 4) {psi : ℝ → ℝ}
    (h : IsCutoff delta psi) : IsAdmissible (1 / 2) (cutoffTest psi) where
  memLp := (cutoffTest_contDiff h).continuous.memLp_of_hasCompactSupport
    (cutoffTest_hasCompactSupport h)
  even := cutoffTest_neg h
  support := fun _ => cutoffTest_eq_zero_of_half_le_abs h
  fourier_sq_zero := fourierC_cutoffTestSq_zero hd hd4 h

/-! ### The kernel sums agree

The double sum over the rescaled zeros and the double sum over the actual
zeros are the same sum, reindexed along the rescaling. Two facts carry it: the rescaling is
injective, so `Finset.sum_image` applies at both levels; and it turns a difference of zeros into
exactly the rescaled difference the pair-correlation formula is stated with.

Stated without an admissibility hypothesis on `eta`: nothing in a reindexing can use it. -/

/-- The rescaling turns a difference of zeros into the rescaled difference. -/
theorem rescale_sub_rescale (T : ℝ) (rho rho' : ℂ) :
    rescale T rho - rescale T rho' = rescaledDiff T rho rho' := by
  simp only [rescale, rescaledDiff]
  ring

/-- **The kernel sums agree** (`lem_kernel_sum_identity`). -/
@[zz_tag "lem_kernel_sum_identity"]
theorem sum_testKernel_sq_eq_finsum_rescaledDiff {T : ℝ} (hT : 1 < T) (eta : ℝ → ℝ) :
    ∑ z ∈ rescaledZerosFinset T, ∑ s ∈ rescaledZerosFinset T,
        ((rescaledMult T z * rescaledMult T s : ℕ) : ℂ) * testKernel eta (z - s) ^ 2 =
      ∑ᶠ rho ∈ nontrivialZeros T, ∑ᶠ rho' ∈ nontrivialZeros T,
        ((zeroMultiplicity rho * zeroMultiplicity rho' : ℕ) : ℂ) *
          testKernel eta (rescaledDiff T rho rho') ^ 2 := by
  classical
  have hinj : ∀ a ∈ (nontrivialZeros_finite T).toFinset,
      ∀ b ∈ (nontrivialZeros_finite T).toFinset, rescale T a = rescale T b → a = b :=
    fun a _ b _ hab => rescale_injective hT hab
  have hinner : ∀ rho : ℂ, ∑ rho' ∈ (nontrivialZeros_finite T).toFinset,
      ((zeroMultiplicity rho * zeroMultiplicity rho' : ℕ) : ℂ) *
          testKernel eta (rescaledDiff T rho rho') ^ 2 =
        ∑ᶠ rho' ∈ nontrivialZeros T,
          ((zeroMultiplicity rho * zeroMultiplicity rho' : ℕ) : ℂ) *
            testKernel eta (rescaledDiff T rho rho') ^ 2 := fun _ => by
    rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
  rw [rescaledZerosFinset]
  simp only [Finset.sum_image hinj, rescaledMult_rescale hT, rescale_sub_rescale, hinner]
  rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]


/-! ### The Fourier transform of the self-convolution

The convolution theorem, at a complex frequency. The move worth keeping is to abstract the
character: the statement holds for any continuous `E : ℝ → ℂ` with
`E (a + b) = E a * E b`, and the complex frequency then stops being special -- no
analytic-continuation argument is needed, only Fubini on the compactly supported integrand.

### The bookkeeping behind the second moment

A double integral whose integrand is a finite double sum with factored terms equals the double sum
of the products of the single integrals. Also stated abstractly. -/

section FourierSelfConv

/-- Abstract version: for any continuous multiplicative character `E`, the "transform" of a
self-convolution factors. -/
theorem selfConv_aux (f : ℝ → ℝ) (hf : Continuous f) (hsupp : HasCompactSupport f)
    (E : ℝ → ℂ) (hEadd : ∀ a b : ℝ, E (a + b) = E a * E b) (hEcont : Continuous E) :
    ∫ x : ℝ, ((∫ t : ℝ, f t * f (x - t) : ℝ) : ℂ) * E x = (∫ u : ℝ, (f u : ℂ) * E u) ^ 2 := by
  set F : ℝ → ℂ := fun u => (f u : ℂ) * E u with hFdef
  have hFcont : Continuous F := (Complex.continuous_ofReal.comp hf).mul hEcont
  have hFsupp : HasCompactSupport F := by
    apply HasCompactSupport.intro hsupp
    intro x hx
    simp [hFdef, image_eq_zero_of_notMem_tsupport hx]
  have hFint : Integrable F := hFcont.integrable_of_hasCompactSupport hFsupp
  have hEsplit : ∀ x t : ℝ, E (x - t) * E t = E x := by
    intro x t
    rw [← hEadd]
    congr 1
    ring
  have hcast : ∀ x : ℝ, ((∫ t : ℝ, f t * f (x - t) : ℝ) : ℂ)
      = ∫ t : ℝ, (f t : ℂ) * (f (x - t) : ℂ) := by
    intro x
    rw [← integral_complex_ofReal]
    simp only [Complex.ofReal_mul]
  have hint2 : Integrable (Function.uncurry fun x t : ℝ => (f t : ℂ) * (f (x - t) : ℂ) * E x)
      ((volume : Measure ℝ).prod volume) := by
    have h1 : Integrable (fun z : ℝ × ℝ => F z.1 * F z.2) ((volume : Measure ℝ).prod volume) :=
      hFint.mul_prod hFint
    have h2 := (measurePreserving_sub_prod (volume : Measure ℝ)
      (volume : Measure ℝ)).integrable_comp_of_integrable h1
    have heq : ((fun z : ℝ × ℝ => F z.1 * F z.2) ∘ fun z : ℝ × ℝ => (z.1 - z.2, z.2))
        = Function.uncurry fun x t : ℝ => (f t : ℂ) * (f (x - t) : ℂ) * E x := by
      funext z
      obtain ⟨x, t⟩ := z
      simp only [Function.comp_apply, Function.uncurry_apply_pair, hFdef]
      rw [← hEsplit x t]
      ring
    rwa [heq] at h2
  calc ∫ x : ℝ, ((∫ t : ℝ, f t * f (x - t) : ℝ) : ℂ) * E x
      = ∫ x : ℝ, ∫ t : ℝ, (f t : ℂ) * (f (x - t) : ℂ) * E x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        change ((∫ t : ℝ, f t * f (x - t) : ℝ) : ℂ) * E x
            = ∫ t : ℝ, (f t : ℂ) * (f (x - t) : ℂ) * E x
        rw [hcast x, ← integral_mul_const]
    _ = ∫ t : ℝ, ∫ x : ℝ, (f t : ℂ) * (f (x - t) : ℂ) * E x := integral_integral_swap hint2
    _ = ∫ t : ℝ, F t * ∫ y : ℝ, F y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        change (∫ x : ℝ, (f t : ℂ) * (f (x - t) : ℂ) * E x) = F t * ∫ y : ℝ, F y
        rw [← integral_add_right_eq_self (fun x => (f t : ℂ) * (f (x - t) : ℂ) * E x) t]
        have hpt : ∀ y : ℝ, (f t : ℂ) * (f (y + t - t) : ℂ) * E (y + t) = F t * F y := by
          intro y
          rw [hEadd]
          simp only [hFdef, add_sub_cancel_right]
          ring
        simp only [hpt]
        exact integral_const_mul _ _
    _ = (∫ u : ℝ, F u) ^ 2 := by rw [integral_mul_const, sq]

/-- **The transform of a self-convolution is the square of the transform.** -/
theorem fourierC_selfConv (f : ℝ → ℝ) (hf : Continuous f) (hsupp : HasCompactSupport f) (ξ : ℂ) :
    fourierC (fun x => ∫ t : ℝ, f t * f (x - t)) ξ = fourierC f ξ ^ 2 := by
  have key := selfConv_aux f hf hsupp
      (fun u : ℝ => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ξ * (u : ℂ)))
      (fun a b => by rw [← Complex.exp_add]; congr 1; push_cast; ring)
      (Complex.continuous_exp.comp (by fun_prop))
  simpa only [fourierC] using key

/-- **A double integral of a factored double sum.** -/
theorem integral_integral_double_sum_factored {iota : Type*} (F : Finset iota) (mu : Measure ℝ)
    (c : iota → iota → ℂ) (a : iota → iota → ℝ → ℂ) (ha : ∀ i j, Integrable (a i j) mu) :
    (∫ u, ∫ v, ∑ i ∈ F, ∑ j ∈ F, c i j * a i j u * a i j v ∂mu ∂mu)
      = ∑ i ∈ F, ∑ j ∈ F, c i j * (∫ u, a i j u ∂mu) * (∫ v, a i j v ∂mu) := by
  have key : ∀ (g : iota → iota → ℂ) (b : iota → iota → ℝ → ℂ),
      (∀ i j, Integrable (b i j) mu) →
      (∫ u, ∑ i ∈ F, ∑ j ∈ F, g i j * b i j u ∂mu)
        = ∑ i ∈ F, ∑ j ∈ F, g i j * ∫ u, b i j u ∂mu := by
    intro g b hb
    rw [integral_finsetSum _
      (fun i _ => integrable_finsetSum _ (fun j _ => (hb i j).const_mul (g i j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hb i j).const_mul (g i j))]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have h2 : ∀ u, (∫ v, ∑ i ∈ F, ∑ j ∈ F, c i j * a i j u * a i j v ∂mu)
      = ∑ i ∈ F, ∑ j ∈ F, (c i j * ∫ v, a i j v ∂mu) * a i j u := by
    intro u
    rw [key (fun i j => c i j * a i j u) a ha]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [show (∫ u, ∫ v, ∑ i ∈ F, ∑ j ∈ F, c i j * a i j u * a i j v ∂mu ∂mu)
      = ∫ u, ∑ i ∈ F, ∑ j ∈ F, (c i j * ∫ v, a i j v ∂mu) * a i j u ∂mu from by
    simp only [h2]]
  rw [key (fun i j => c i j * ∫ v, a i j v ∂mu) a ha]

/-! ### The two instantiations -/

/-- **The transform of `Q_psi` is the square of the kernel** (`lem_Q_psi_hat`). -/
@[zz_tag "lem_Q_psi_hat"]
theorem fourierC_cutoffSelfConv {delta : ℝ} {psi : ℝ → ℝ} (h : IsCutoff delta psi) (z : ℂ) :
    fourierC (cutoffSelfConv psi) z = testKernel (cutoffTest psi) z ^ 2 := by
  have hQ : cutoffSelfConv psi
      = fun x => ∫ t : ℝ, cutoffTestSq psi t * cutoffTestSq psi (x - t) := rfl
  rw [hQ, fourierC_selfConv _ (cutoffTestSq_contDiff h).continuous
    (cutoffTestSq_hasCompactSupport h) z]
  rfl

/-- A twisted function against another twisted function's conjugate is integrable.

Distinct from the existing `integrable_fz_mul_conj`, which pairs against an `L²` ELEMENT. That
one is not syntactically usable here: `(fzL2 h s : ℝ → ℂ)` is only a.e. equal to `fz eta s`, so
applying it would need an `Integrable.congr` where `memLp_fz` directly needs nothing. -/
theorem integrable_fz_mul_conj_fz (h : IsAdmissible lam eta) (z s : ℂ) :
    Integrable (fun u => fz eta z u * (starRingEnd ℂ) (fz eta s u))
      (volume.restrict (Set.Ioo (-lam) lam)) :=
  (memLp_fz h z).integrable_mul ((memLp_fz h s).star)

/-- **The second moment is the `L²(I²)` norm of the two-variable kernel** (`lem_second_moment`). -/
@[zz_tag "lem_second_moment"]
theorem sum_testKernel_sq_eq_integral_bigF_mul_conj (h : IsAdmissible lam eta)
    (Z : Finset ℂ) (m : ℂ → ℕ) :
    ∑ z ∈ Z, ∑ s ∈ Z, ((m z * m s : ℕ) : ℂ) * testKernel eta (z - (starRingEnd ℂ) s) ^ 2 =
      ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        bigF eta Z m u v * (starRingEnd ℂ) (bigF eta Z m u v) := by
  classical
  have hexp : ∀ u v : ℝ, bigF eta Z m u v * (starRingEnd ℂ) (bigF eta Z m u v)
      = ∑ z ∈ Z, ∑ t ∈ Z, ((m t * m z : ℕ) : ℂ) *
          (fz eta t u * (starRingEnd ℂ) (fz eta z u)) *
            (fz eta t v * (starRingEnd ℂ) (fz eta z v)) := by
    intro u v
    simp only [bigF, map_sum, Finset.sum_mul, Finset.mul_sum, map_mul, Complex.conj_natCast,
      Nat.cast_mul]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => by ring
  simp only [hexp]
  rw [integral_integral_double_sum_factored Z _ (fun z t => ((m t * m z : ℕ) : ℂ))
    (fun z t u => fz eta t u * (starRingEnd ℂ) (fz eta z u))
    (fun z t => integrable_fz_mul_conj_fz h t z), Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun z _ => by
    rw [testKernel_sub_conj h z s]; ring

end FourierSelfConv

/-! ### Bessel's inequality for the two-variable kernel

The abstract inequality is `sum_sq_pairing_le_integral_norm_sq`, and the orthonormality of the
tensor squares is `integral_tensor_square_pairing`. What is left is the integrability, which is
proved here rather than assumed as a hypothesis.

`bigF` is a finite sum of tensor products, so `memLp_tensor_two` on each summand and
`memLp_finsetSum` over `Z` does it; the basis members give their tensor squares the same way.

Realness of the coefficients is not needed. The usual argument invokes `alphaCoeff_im_eq_zero` to
turn `|alpha_j|^2` into `alpha_j^2`; but the norm form is the stronger inequality and
`(re a)^2 ≤ ‖a‖^2` holds for every complex `a`, so the real-coefficient form follows with no appeal
to realness, no conjugation-invariance and no symmetry hypothesis. That matters practically:
`alphaCoeff_im_eq_zero` wants pointwise `IsSymmetric`, whereas a Gram--Schmidt basis is only
symmetric almost everywhere. -/

/-- The two-variable kernel is `L²` on the square: it is a finite sum of tensor products. -/
theorem memLp_bigF (h : IsAdmissible lam eta) (Z : Finset ℂ) (m : ℂ → ℕ) :
    MemLp (fun p : ℝ × ℝ => bigF eta Z m p.1 p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))) := by
  have hsum : (fun p : ℝ × ℝ => bigF eta Z m p.1 p.2)
      = fun p : ℝ × ℝ => ∑ z ∈ Z, ((m z : ℂ) * fz eta z p.1) * fz eta z p.2 := rfl
  rw [hsum]
  exact memLp_finsetSum Z fun z _ =>
    memLp_tensor_two ((memLp_fz h z).const_mul (m z : ℂ)) (memLp_fz h z)

/-- The tensor square of an `L²` element is `L²` on the square. -/
theorem memLp_tensor_square (psi : L2Interval lam) :
    MemLp (fun p : ℝ × ℝ => (psi : ℝ → ℂ) p.1 * (psi : ℝ → ℂ) p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod (volume.restrict (Set.Ioo (-lam) lam))) :=
  memLp_tensor_two (Lp.memLp psi) (Lp.memLp psi)

/-- **Bessel's inequality for the kernel, in norm form.** Stronger than the real-coefficient form,
and what actually gets proved. -/
theorem sum_norm_alphaOf_sq_le_integral_norm_bigF_sq (h : IsAdmissible lam eta) {Z : Finset ℂ}
    {m : ℂ → ℕ} {N : ℕ} (psi : Fin N → L2Interval lam) (horth : Orthonormal ℂ psi) :
    ∑ j, ‖alphaOf eta lam Z m (psi j)‖ ^ 2
      ≤ ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam, ‖bigF eta Z m u v‖ ^ 2 := by
  classical
  exact sum_sq_pairing_le_integral_norm_sq (bigF eta Z m) (fun j => (psi j : ℝ → ℂ))
    (memLp_bigF h Z m) (fun j => memLp_tensor_square (psi j))
    (fun j l => integral_tensor_square_pairing psi horth j l)

/-- **Bessel's inequality for the kernel** (`lem_bessel_F`).

Stated without conjugation-invariance of `(Z, m)` and without symmetry of the basis members: the
norm form above needs neither, and `(re a)^2 <= ‖a‖^2` delivers this from it. -/
@[zz_tag "lem_bessel_F"]
theorem sum_alphaOf_re_sq_le_integral_norm_bigF_sq (h : IsAdmissible lam eta) {Z : Finset ℂ}
    {m : ℂ → ℕ} {N : ℕ} (psi : Fin N → L2Interval lam) (horth : Orthonormal ℂ psi) :
    ∑ j, (alphaOf eta lam Z m (psi j)).re ^ 2
      ≤ ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam, ‖bigF eta Z m u v‖ ^ 2 := by
  refine le_trans (Finset.sum_le_sum fun j _ => ?_)
    (sum_norm_alphaOf_sq_le_integral_norm_bigF_sq h psi horth)
  have hn : ‖alphaOf eta lam Z m (psi j)‖ ^ 2
      = (alphaOf eta lam Z m (psi j)).re ^ 2 + (alphaOf eta lam Z m (psi j)).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hn]
  nlinarith [sq_nonneg (alphaOf eta lam Z m (psi j)).im]

/-! ### The rescaled multiset is conjugation-invariant

The composite symmetry `rho ↦ 1 - conj rho` is what makes the rescaled zeros conjugation-invariant.
Both halves are available: `zeroMultiplicity_conj` for conjugation and `zeroMultiplicity_one_sub`
for the reflection.

The computation is that conjugating a rescaled zero rescales the REFLECTED CONJUGATE:
`conj (rescale T rho) = rescale T (1 - conj rho)`. Everything else follows, and the vanishing of
zeta at `1 - conj rho` comes straight from the functional equation rather than through the
multiplicity -- `zeta (conj rho) = conj (zeta rho) = 0`, so the product form vanishes. -/

/-- Conjugating a rescaled point rescales the reflected conjugate. -/
theorem conj_rescale (T : ℝ) (rho : ℂ) :
    (starRingEnd ℂ) (rescale T rho) = rescale T (1 - (starRingEnd ℂ) rho) := by
  simp only [rescale, map_mul, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal,
    map_div₀, map_ofNat]
  ring

/-- The reflected conjugate of a non-trivial zero is a non-trivial zero at the same height. -/
theorem one_sub_conj_mem_nontrivialZeros {T : ℝ} {rho : ℂ} (hrho : rho ∈ nontrivialZeros T) :
    1 - (starRingEnd ℂ) rho ∈ nontrivialZeros T := by
  obtain ⟨hzero, hre0, hre1, him0, himT⟩ := hrho
  have hzc : riemannZeta ((starRingEnd ℂ) rho) = 0 := by
    rw [riemannZeta_conj, hzero, map_zero]
  have hne1 : (starRingEnd ℂ) rho ≠ 1 := by
    intro hEq
    have : ((starRingEnd ℂ) rho).re = 1 := by rw [hEq]; simp
    rw [Complex.conj_re] at this
    linarith
  have hnen : ∀ n : ℕ, (starRingEnd ℂ) rho ≠ -(n : ℂ) := by
    intro n hEq
    have : ((starRingEnd ℂ) rho).re = -(n : ℝ) := by rw [hEq]; simp
    rw [Complex.conj_re] at this
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [riemannZeta_one_sub hnen hne1, hzc, mul_zero]
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simpa [Complex.sub_im, Complex.conj_im] using him0
  · simpa [Complex.sub_im, Complex.conj_im] using himT

/-- The multiplicity is unchanged by the composite symmetry. -/
theorem zeroMultiplicity_one_sub_conj {rho : ℂ} (hre0 : 0 < rho.re) (hre1 : rho.re < 1) :
    zeroMultiplicity (1 - (starRingEnd ℂ) rho) = zeroMultiplicity rho := by
  have hne1 : rho ≠ 1 := fun hEq => by rw [hEq] at hre1; simp at hre1
  rw [zeroMultiplicity_one_sub (by simpa [Complex.conj_re] using hre0)
    (by simpa [Complex.conj_re] using hre1), zeroMultiplicity_conj hne1]

/-- **The rescaled multiset is conjugation-invariant** (`lem_Z_T_conj`). -/
@[zz_tag "lem_Z_T_conj"]
theorem isConjInvariant_rescaledZerosFinset {T : ℝ} (hT : 1 < T) :
    IsConjInvariant (rescaledZerosFinset T) (rescaledMult T) where
  one_le := by
    classical
    intro z hz
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset] at hz
    obtain ⟨rho, hrho, rfl⟩ := hz
    rw [rescaledMult_rescale hT]
    exact one_le_zeroMultiplicity hrho
  conj_mem := by
    classical
    intro z hz
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset] at hz ⊢
    obtain ⟨rho, hrho, rfl⟩ := hz
    exact ⟨1 - (starRingEnd ℂ) rho, one_sub_conj_mem_nontrivialZeros hrho,
      (conj_rescale T rho).symm⟩
  mult_conj := by
    classical
    intro z hz
    simp only [rescaledZerosFinset, Finset.mem_image, Set.Finite.mem_toFinset] at hz
    obtain ⟨rho, hrho, rfl⟩ := hz
    rw [conj_rescale, rescaledMult_rescale hT, rescaledMult_rescale hT,
      zeroMultiplicity_one_sub_conj hrho.2.1 hrho.2.2.1]

/-- The tensor square of an `L²` function belongs to `L²` for the product measure. -/
theorem memLp_tensor_square_of_memLp {lam : ℝ} {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioo (-lam) lam))) :
    MemLp (fun p : ℝ × ℝ => f p.1 * f p.2) 2
      ((volume.restrict (Set.Ioo (-lam) lam)).prod
        (volume.restrict (Set.Ioo (-lam) lam))) :=
  memLp_tensor_two hf hf


/-! ## The kernel second moment -/

/-- Expanding `F * conj F` gives the sum over ordered pairs of support points. -/
private lemma sum_pair_fz_mul_conj_eq_bigF_mul_conj_alpha
    (Z : Finset ℂ) (m : ℂ → ℕ) (u v : ℝ) :
    ∑ p ∈ Z ×ˢ Z, (m p.1 * m p.2 : ℂ) *
        (fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u)) *
        (fz eta p.1 v * (starRingEnd ℂ) (fz eta p.2 v))
      = bigF eta Z m u v * (starRingEnd ℂ) (bigF eta Z m u v) := by
  simp only [Finset.sum_product, bigF, map_sum, map_mul, Complex.conj_natCast]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

/-- The unconjugated finite kernel sum is the product-space second moment of `bigF`.

The Gram identity initially conjugates the second support point; conjugation invariance permits
the change of variables back to the difference `z - s`. -/
theorem sum_testKernel_sq_eq_integral_norm_bigF_sq
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) :
    ∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          ((‖bigF eta Z m u v‖ ^ 2 : ℝ) : ℂ) := by
  rw [sum_testKernel_sq_eq_sum_conj hZ]
  have hint : ∀ p ∈ Z ×ˢ Z,
      Integrable
        (fun u => (fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u)) * (1 : ℂ))
        (volume.restrict (Set.Ioo (-lam) lam)) := by
    intro p hp
    simp only [mul_one]
    change Integrable (fz eta p.1 * star (fz eta p.2))
      (volume.restrict (Set.Ioo (-lam) lam))
    exact (memLp_fz h p.1).integrable_mul (memLp_fz h p.2).star
  have hfactor := integral_double_finsetSum (Z ×ˢ Z)
    (fun p => (m p.1 * m p.2 : ℂ))
    (fun p u => fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u))
    (fun _ => (1 : ℂ)) lam hint
  simp only [mul_one] at hfactor
  calc
    (∑ z ∈ Z, ∑ s ∈ Z,
        (m z * m s : ℂ) * testKernel eta (z - (starRingEnd ℂ) s) ^ 2) =
        ∑ p ∈ Z ×ˢ Z, (m p.1 * m p.2 : ℂ) *
          (∫ u in Set.Ioo (-lam) lam,
            fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u)) ^ 2 := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro s hs
      rw [testKernel_sub_conj h z s]
    _ = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        ∑ p ∈ Z ×ˢ Z, (m p.1 * m p.2 : ℂ) *
          (fz eta p.1 u * (starRingEnd ℂ) (fz eta p.2 u)) *
          (fz eta p.1 v * (starRingEnd ℂ) (fz eta p.2 v)) := hfactor.symm
    _ = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        bigF eta Z m u v * (starRingEnd ℂ) (bigF eta Z m u v) := by
      apply integral_congr_ae
      filter_upwards [] with u
      apply integral_congr_ae
      filter_upwards [] with v
      exact sum_pair_fz_mul_conj_eq_bigF_mul_conj_alpha Z m u v
    _ = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
        ((‖bigF eta Z m u v‖ ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with u
      apply integral_congr_ae
      filter_upwards [] with v
      rw [Complex.mul_conj']
      norm_cast

/-- Real-valued form of the second-moment identity, matching the right side of Bessel's
inequality. -/
theorem sum_testKernel_sq_re_eq_integral_norm_bigF_sq
    (h : IsAdmissible lam eta) (hZ : IsConjInvariant Z m) :
    (∑ z ∈ Z, ∑ s ∈ Z, (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      = ∫ u in Set.Ioo (-lam) lam, ∫ v in Set.Ioo (-lam) lam,
          ‖bigF eta Z m u v‖ ^ 2 := by
  rw [sum_testKernel_sq_eq_integral_norm_bigF_sq h hZ]
  simp only [integral_complex_ofReal, Complex.ofReal_re]

/-! ## The first-range coefficient estimate -/

/-- The real part of one coefficient expressed entirely in squared Hilbert-space pairings.

This is the common pointwise form used by the Parseval/Bessel arguments for the three basis
ranges.  Symmetry makes all the pairings real, so the real part of their complex squares is their
squared norm. -/
theorem alphaOf_re_eq_sum_norm (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) {phi : L2Interval lam}
    (hsym : IsSymmetricL2 phi) :
    (alphaOf eta lam Z m phi).re
      = (∑ x ∈ simpleRealPart Z m ∪ multipleRealPart Z m,
          (m x : ℝ) * ‖inner ℂ phi (fzL2 h x)‖ ^ 2)
        + ∑ z ∈ nonRealPart Z, (m z : ℝ) *
            (‖inner ℂ phi (gzL2 h z)‖ ^ 2 - ‖inner ℂ phi (hzL2 h z)‖ ^ 2) := by
  classical
  rw [alphaOf_eq h hZ, Complex.add_re, Complex.re_sum, Complex.re_sum]
  congr 1
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hxre : x.im = 0 := by
      rcases Finset.mem_union.mp hx with hx' | hx'
      · exact ((Finset.mem_filter.mp hx').2).1
      · exact ((Finset.mem_filter.mp hx').2).1
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_fzL2 h x)]
    refine natCast_mul_sq_re ?_ _
    exact inner_symmetricL2_im_eq_zero hsym (fzL2_mem_symmetricSubspace h hxre)
  · refine Finset.sum_congr rfl fun z _ => ?_
    have hgim : (inner ℂ phi (gzL2 h z) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (gzL2_mem_symmetricSubspace h z)
    have hhim : (inner ℂ phi (hzL2 h z) : ℂ).im = 0 :=
      inner_symmetricL2_im_eq_zero hsym (hzL2_mem_symmetricSubspace h z)
    rw [integral_mul_conj_eq_inner_of_ae (coeFn_gzL2 h z),
      integral_mul_conj_eq_inner_of_ae (coeFn_hzL2 h z)]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im, sq,
      Complex.natCast_re, Complex.natCast_im, hgim, hhim]
    ring

/-- **First range: lower bound for the coefficient sum** (`lem_alpha_first_lower`).

Parseval on the initial segment spanning `U` is exact for the `f_x` at multiple real points and
the `g_z` at non-real points.  Bessel bounds the subtracted `h_z` terms, leaving the unit norm
defect.  Finally multiplicities are at least two on `R₂` and at least one on the support. -/
@[zz_tag "lem_alpha_first_lower"]
theorem sum_alphaOf_re_first_lower (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m)
    {psi : Fin (Module.finrank ℂ (subspaceW h Z m)) → L2Interval lam}
    (hb : IsAdaptedBasis h Z m psi) (hsym : ∀ j, IsSymmetricL2 (psi j)) :
    2 * ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
      ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
          (j : ℕ) < Module.finrank ℂ (subspaceU h Z m)),
        (alphaOf eta lam Z m (psi j)).re := by
  classical
  let s := Finset.univ.filter (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
    (j : ℕ) < Module.finrank ℂ (subspaceU h Z m))
  have hspan : Submodule.span ℂ (psi '' (s : Set _)) = subspaceU h Z m := by
    simpa [s] using hb.span_U
  have hfz : ∀ x ∈ multipleRealPart Z m,
      fzL2 h x ∈ Submodule.span ℂ (psi '' (s : Set _)) := by
    intro x hx
    rw [hspan, subspaceU]
    exact Submodule.subset_span (Set.mem_union_left _ ⟨x, by simpa using hx, rfl⟩)
  have hgz : ∀ z ∈ nonRealPart Z,
      gzL2 h z ∈ Submodule.span ℂ (psi '' (s : Set _)) := by
    intro z hz
    rw [hspan, subspaceU]
    exact Submodule.subset_span (Set.mem_union_right _ ⟨z, by simpa using hz, rfl⟩)
  have hone_f : ∀ x ∈ multipleRealPart Z m,
      ∑ j ∈ s, ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 = 1 := by
    intro x hx
    rw [sum_sq_norm_inner_eq_norm_sq_of_mem_span_finset hb.orthonormal s (hfz x hx)]
    exact norm_fzL2_sq_eq_one h ((Finset.mem_filter.mp hx).2).1
  have hg_parseval : ∀ z ∈ nonRealPart Z,
      ∑ j ∈ s, ‖inner ℂ (psi j) (gzL2 h z)‖ ^ 2 = ‖gzL2 h z‖ ^ 2 := by
    intro z hz
    exact sum_sq_norm_inner_eq_norm_sq_of_mem_span_finset hb.orthonormal s (hgz z hz)
  have hh_bessel : ∀ z : ℂ,
      ∑ j ∈ s, ‖inner ℂ (psi j) (hzL2 h z)‖ ^ 2 ≤ ‖hzL2 h z‖ ^ 2 := by
    intro z
    exact hb.orthonormal.sum_inner_products_le (s := s) (hzL2 h z)
  rw [show (∑ j ∈ Finset.univ.filter
      (fun j : Fin (Module.finrank ℂ (subspaceW h Z m)) =>
        (j : ℕ) < Module.finrank ℂ (subspaceU h Z m)),
      (alphaOf eta lam Z m (psi j)).re) =
      ∑ j ∈ s, (alphaOf eta lam Z m (psi j)).re by rfl]
  simp_rw [alphaOf_re_eq_sum_norm h hZ (hsym _)]
  rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (s := s) (t := nonRealPart Z)]
  have hR1nonneg : 0 ≤ ∑ x ∈ simpleRealPart Z m,
      ∑ j ∈ s, (m x : ℝ) * ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2 := by positivity
  rw [Finset.sum_union disjoint_simpleRealPart_multipleRealPart]
  have hR2 : ∑ x ∈ multipleRealPart Z m,
      ∑ j ∈ s, (m x : ℝ) * ‖inner ℂ (psi j) (fzL2 h x)‖ ^ 2
      = ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.mul_sum, hone_f x hx, mul_one]
  rw [hR2]
  have hS : ∑ z ∈ nonRealPart Z,
      ∑ j ∈ s, (m z : ℝ) *
        (‖inner ℂ (psi j) (gzL2 h z)‖ ^ 2 - ‖inner ℂ (psi j) (hzL2 h z)‖ ^ 2)
      ≥ ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
    refine Finset.sum_le_sum fun z hz => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hg_parseval z hz]
    have hm : (0 : ℝ) ≤ (m z : ℝ) := by positivity
    have hd := hh_bessel z
    have hdef := norm_gzL2_sq_sub_norm_hzL2_sq h z
    nlinarith
  have hR2card : 2 * ((multipleRealPart Z m).card : ℝ)
      ≤ ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
    calc
      2 * ((multipleRealPart Z m).card : ℝ)
          = ∑ _x ∈ multipleRealPart Z m, (2 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        exact_mod_cast ((Finset.mem_filter.mp hx).2).2
  have hScard : ((nonRealPart Z).card : ℝ)
      ≤ ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
    calc
      ((nonRealPart Z).card : ℝ) = ∑ _z ∈ nonRealPart Z, (1 : ℝ) := by simp
      _ ≤ ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
        refine Finset.sum_le_sum fun z hz => ?_
        exact_mod_cast hZ.one_le z (Finset.mem_filter.mp hz).1
  linarith

/-! ## Three-range algebra -/

/-- The numerical three-range estimate used for the simple-real-point bound.

The first range uses `a² + 4 ≥ 4a`, the middle range uses `a² + 1 ≥ 2a`, and the
last range uses `a ≤ 0`. -/
theorem three_range_simple {N dU dV R1 R2 S : ℕ} (a : Fin N → ℝ)
    (hdUV : dU ≤ dV) (hdVN : dV ≤ N)
    (hdU : dU ≤ R2 + S / 2) (hdGap : dV ≤ dU + R1)
    (hfirst : 2 * (R2 : ℝ) + (S : ℝ) ≤
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU), a j)
    (hthird : ∀ j : Fin N, dV ≤ (j : ℕ) → a j ≤ 0) :
    2 * ∑ j, a j - (R1 : ℝ) ≤ ∑ j, a j ^ 2 := by
  classical
  let A := Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU)
  let B := Finset.univ.filter (fun j : Fin N => dU ≤ (j : ℕ) ∧ (j : ℕ) < dV)
  let C := Finset.univ.filter (fun j : Fin N => dV ≤ (j : ℕ))
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjA hjB
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
    omega
  have hABC : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjAB hjC
    rw [Finset.mem_union] at hjAB
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hjC
    rcases hjAB with hjA | hjB
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
      omega
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
      omega
  have hcover : A ∪ B ∪ C = Finset.univ := by
    ext j
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    omega
  have hABeq : A ∪ B = Finset.univ.filter (fun j : Fin N => (j : ℕ) < dV) := by
    ext j
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcardA : A.card = dU := by
    rw [show A = Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU) from rfl,
      Fin.card_filter_val_lt, Nat.min_eq_right (le_trans hdUV hdVN)]
  have hcardAB : (A ∪ B).card = dV := by
    rw [hABeq, Fin.card_filter_val_lt, Nat.min_eq_right hdVN]
  have hcardB_le : B.card ≤ R1 := by
    rw [Finset.card_union_of_disjoint hAB, hcardA] at hcardAB
    omega
  have htwodim_nat : 2 * dU ≤ 2 * R2 + S := by
    omega
  have htwodim : 2 * (dU : ℝ) ≤ 2 * (R2 : ℝ) + (S : ℝ) := by
    exact_mod_cast htwodim_nat
  have hsqA_base :
      4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ) ≤ ∑ j ∈ A, a j ^ 2 := by
    calc
      4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ)
          = ∑ j ∈ A, (4 * a j - 4) := by simp [Finset.mul_sum]; ring
      _ ≤ ∑ j ∈ A, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        nlinarith [sq_nonneg (a j - 2)]
  have hsqA : 2 * (∑ j ∈ A, a j) ≤ ∑ j ∈ A, a j ^ 2 := by
    rw [hcardA] at hsqA_base
    have hfirstA : 2 * (R2 : ℝ) + (S : ℝ) ≤ ∑ j ∈ A, a j := by
      exact hfirst
    nlinarith
  have hsqB_base :
      2 * (∑ j ∈ B, a j) - (B.card : ℝ) ≤ ∑ j ∈ B, a j ^ 2 := by
    calc
      2 * (∑ j ∈ B, a j) - (B.card : ℝ)
          = ∑ j ∈ B, (2 * a j - 1) := by simp [Finset.mul_sum]
      _ ≤ ∑ j ∈ B, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        nlinarith [sq_nonneg (a j - 1)]
  have hcardB_real : (B.card : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hcardB_le
  have hsqB : 2 * (∑ j ∈ B, a j) - (R1 : ℝ) ≤ ∑ j ∈ B, a j ^ 2 := by
    linarith
  have hsqC : 2 * (∑ j ∈ C, a j) ≤ ∑ j ∈ C, a j ^ 2 := by
    calc
      2 * (∑ j ∈ C, a j) = ∑ j ∈ C, 2 * a j := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ C, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : dV ≤ (j : ℕ) := by simpa [C] using hj
        have ha := hthird j hj'
        nlinarith [sq_nonneg (a j)]
  have hsum (f : Fin N → ℝ) :
      ∑ j, f j = (∑ j ∈ A, f j) + (∑ j ∈ B, f j) + ∑ j ∈ C, f j := by
    rw [← hcover, Finset.sum_union hABC, Finset.sum_union hAB]
  rw [hsum a, hsum (fun j => a j ^ 2)]
  linarith

/-- **Lower bound for the simple real elements** (`prop_simple_real_lower`). -/
@[zz_tag "prop_simple_real_lower"]
theorem card_simpleRealPart_lower (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) :
    2 * (∑ z ∈ Z, (m z : ℝ))
        - (∑ z ∈ Z, ∑ s ∈ Z,
            (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ ((simpleRealPart Z m).card : ℝ) := by
  classical
  obtain ⟨psi, hb, hsym⟩ := exists_symmetric_adapted_basis h Z m
  let a : Fin (Module.finrank ℂ (subspaceW h Z m)) → ℝ :=
    fun j => (alphaOf eta lam Z m (psi j)).re
  have hdUV : Module.finrank ℂ (subspaceU h Z m) ≤
      Module.finrank ℂ (subspaceV h Z m) :=
    Submodule.finrank_mono (subspaceU_le_subspaceV h Z m)
  have hdVN : Module.finrank ℂ (subspaceV h Z m) ≤
      Module.finrank ℂ (subspaceW h Z m) :=
    Submodule.finrank_mono (subspaceV_le_subspaceW h Z m)
  have hrange := three_range_simple a hdUV hdVN
    (finrank_subspaceU_le h hZ) (finrank_subspaceV_le h Z m)
    (sum_alphaOf_re_first_lower h hZ hb hsym)
    (fun j hj => alphaOf_re_nonpos h hZ hb (hsym j) hj)
  have htotal := sum_alphaOf_re_eq_sum_mult h hZ hb hsym
  have hbessel := sum_alphaOf_re_sq_le_integral_norm_bigF_sq (Z := Z) (m := m)
    h psi hb.orthonormal
  have hmoment := sum_testKernel_sq_re_eq_integral_norm_bigF_sq h hZ
  change 2 * (∑ j, a j) - ((simpleRealPart Z m).card : ℝ)
      ≤ ∑ j, a j ^ 2 at hrange
  change ∑ j, a j = ∑ z ∈ Z, (m z : ℝ) at htotal
  change ∑ j, a j ^ 2 ≤ _ at hbessel
  rw [← hmoment] at hbessel
  linarith

/-- The numerical three-range estimate used for the distinct-point bound.

Compared with `three_range_simple`, all three ranges retain a factor four.  On the middle range,
the upper bound on its coefficient sum supplies the extra factor two. -/
theorem three_range_distinct {N dU dV R1 R2 S : ℕ} (a : Fin N → ℝ)
    (hdUV : dU ≤ dV) (hdVN : dV ≤ N)
    (hdU : dU ≤ R2 + S / 2) (hdGap : dV ≤ dU + R1)
    (hsecond :
      ∑ j ∈ Finset.univ.filter
          (fun j : Fin N => dU ≤ (j : ℕ) ∧ (j : ℕ) < dV), a j
        ≤ (R1 : ℝ))
    (hthird : ∀ j : Fin N, dV ≤ (j : ℕ) → a j ≤ 0)
    (hmult : (R1 : ℝ) + 2 * (R2 : ℝ) + (S : ℝ) ≤ ∑ j, a j) :
    3 * ∑ j, a j - 2 * ((R1 : ℝ) + (R2 : ℝ) + (S : ℝ))
      ≤ ∑ j, a j ^ 2 := by
  classical
  let A := Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU)
  let B := Finset.univ.filter (fun j : Fin N => dU ≤ (j : ℕ) ∧ (j : ℕ) < dV)
  let C := Finset.univ.filter (fun j : Fin N => dV ≤ (j : ℕ))
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjA hjB
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
    omega
  have hABC : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.mpr ?_
    intro j hjAB hjC
    rw [Finset.mem_union] at hjAB
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hjC
    rcases hjAB with hjA | hjB
    · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hjA
      omega
    · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hjB
      omega
  have hcover : A ∪ B ∪ C = Finset.univ := by
    ext j
    simp only [A, B, C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    omega
  have hABeq : A ∪ B = Finset.univ.filter (fun j : Fin N => (j : ℕ) < dV) := by
    ext j
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hcardA : A.card = dU := by
    rw [show A = Finset.univ.filter (fun j : Fin N => (j : ℕ) < dU) from rfl,
      Fin.card_filter_val_lt, Nat.min_eq_right (le_trans hdUV hdVN)]
  have hcardAB : (A ∪ B).card = dV := by
    rw [hABeq, Fin.card_filter_val_lt, Nat.min_eq_right hdVN]
  have hcardB_le : B.card ≤ R1 := by
    rw [Finset.card_union_of_disjoint hAB, hcardA] at hcardAB
    omega
  have hfourdim_nat : 4 * dU ≤ 4 * R2 + 2 * S := by
    omega
  have hfourdim : 4 * (dU : ℝ) ≤ 4 * (R2 : ℝ) + 2 * (S : ℝ) := by
    exact_mod_cast hfourdim_nat
  have hsqA_base :
      4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ) ≤ ∑ j ∈ A, a j ^ 2 := by
    calc
      4 * (∑ j ∈ A, a j) - 4 * (A.card : ℝ)
          = ∑ j ∈ A, (4 * a j - 4) := by simp [Finset.mul_sum]; ring
      _ ≤ ∑ j ∈ A, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        nlinarith [sq_nonneg (a j - 2)]
  have hsqA :
      4 * (∑ j ∈ A, a j) - 4 * (R2 : ℝ) - 2 * (S : ℝ)
        ≤ ∑ j ∈ A, a j ^ 2 := by
    rw [hcardA] at hsqA_base
    linarith
  have hsqB_base :
      2 * (∑ j ∈ B, a j) - (B.card : ℝ) ≤ ∑ j ∈ B, a j ^ 2 := by
    calc
      2 * (∑ j ∈ B, a j) - (B.card : ℝ)
          = ∑ j ∈ B, (2 * a j - 1) := by simp [Finset.mul_sum]
      _ ≤ ∑ j ∈ B, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        nlinarith [sq_nonneg (a j - 1)]
  have hcardB_real : (B.card : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hcardB_le
  have hsecondB : (∑ j ∈ B, a j) ≤ (R1 : ℝ) := by exact hsecond
  have hsqB : 4 * (∑ j ∈ B, a j) - 3 * (R1 : ℝ)
      ≤ ∑ j ∈ B, a j ^ 2 := by
    linarith
  have hsqC : 4 * (∑ j ∈ C, a j) ≤ ∑ j ∈ C, a j ^ 2 := by
    calc
      4 * (∑ j ∈ C, a j) = ∑ j ∈ C, 4 * a j := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ C, a j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : dV ≤ (j : ℕ) := by simpa [C] using hj
        have ha := hthird j hj'
        nlinarith [sq_nonneg (a j)]
  have hsum (f : Fin N → ℝ) :
      ∑ j, f j = (∑ j ∈ A, f j) + (∑ j ∈ B, f j) + ∑ j ∈ C, f j := by
    rw [← hcover, Finset.sum_union hABC, Finset.sum_union hAB]
  rw [hsum a] at hmult ⊢
  rw [hsum (fun j => a j ^ 2)]
  linarith

/-- **Lower bound for the distinct elements** (`prop_distinct_lower`). -/
@[zz_tag "prop_distinct_lower"]
theorem card_lower (h : IsAdmissible lam eta)
    (hZ : IsConjInvariant Z m) :
    (3 / 2 : ℝ) * (∑ z ∈ Z, (m z : ℝ))
        - (1 / 2 : ℝ) *
          (∑ z ∈ Z, ∑ s ∈ Z,
            (m z * m s : ℂ) * testKernel eta (z - s) ^ 2).re
      ≤ (Z.card : ℝ) := by
  classical
  obtain ⟨psi, hb, hsym⟩ := exists_symmetric_adapted_basis h Z m
  let a : Fin (Module.finrank ℂ (subspaceW h Z m)) → ℝ :=
    fun j => (alphaOf eta lam Z m (psi j)).re
  have hdUV : Module.finrank ℂ (subspaceU h Z m) ≤
      Module.finrank ℂ (subspaceV h Z m) :=
    Submodule.finrank_mono (subspaceU_le_subspaceV h Z m)
  have hdVN : Module.finrank ℂ (subspaceV h Z m) ≤
      Module.finrank ℂ (subspaceW h Z m) :=
    Submodule.finrank_mono (subspaceV_le_subspaceW h Z m)
  have hR1mult : ((simpleRealPart Z m).card : ℝ) =
      ∑ x ∈ simpleRealPart Z m, (m x : ℝ) := by
    calc
      ((simpleRealPart Z m).card : ℝ) =
          ∑ _x ∈ simpleRealPart Z m, (1 : ℝ) := by simp
      _ = ∑ x ∈ simpleRealPart Z m, (m x : ℝ) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        exact_mod_cast ((Finset.mem_filter.mp hx).2).2.symm
  have hR2mult : 2 * ((multipleRealPart Z m).card : ℝ) ≤
      ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
    calc
      2 * ((multipleRealPart Z m).card : ℝ) =
          ∑ _x ∈ multipleRealPart Z m, (2 : ℝ) := by simp [mul_comm]
      _ ≤ ∑ x ∈ multipleRealPart Z m, (m x : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        exact_mod_cast ((Finset.mem_filter.mp hx).2).2
  have hSmult : ((nonRealPart Z).card : ℝ) ≤
      ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
    calc
      ((nonRealPart Z).card : ℝ) =
          ∑ _z ∈ nonRealPart Z, (1 : ℝ) := by simp
      _ ≤ ∑ z ∈ nonRealPart Z, (m z : ℝ) := by
        refine Finset.sum_le_sum fun z hz => ?_
        exact_mod_cast hZ.one_le z (Finset.mem_filter.mp hz).1
  have hmult : ((simpleRealPart Z m).card : ℝ)
        + 2 * ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
      ≤ ∑ z ∈ Z, (m z : ℝ) := by
    calc
      ((simpleRealPart Z m).card : ℝ)
            + 2 * ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
          ≤ (∑ x ∈ simpleRealPart Z m, (m x : ℝ))
              + (∑ x ∈ multipleRealPart Z m, (m x : ℝ))
              + ∑ z ∈ nonRealPart Z, (m z : ℝ) := by linarith
      _ = ∑ z ∈ Z, (m z : ℝ) := by
        rw [← Finset.sum_union disjoint_simpleRealPart_multipleRealPart,
          ← Finset.sum_union disjoint_realPart_nonRealPart,
          union_realPart_nonRealPart hZ]
  have htotal := sum_alphaOf_re_eq_sum_mult h hZ hb hsym
  change ∑ j, a j = ∑ z ∈ Z, (m z : ℝ) at htotal
  have hmult_a : ((simpleRealPart Z m).card : ℝ)
        + 2 * ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
      ≤ ∑ j, a j := by
    rw [htotal]
    exact hmult
  have hrange := three_range_distinct a hdUV hdVN
    (finrank_subspaceU_le h hZ) (finrank_subspaceV_le h Z m)
    (sum_alphaOf_re_le_card_simpleRealPart h hZ hb hsym)
    (fun j hj => alphaOf_re_nonpos h hZ hb (hsym j) hj) hmult_a
  have hbessel := sum_alphaOf_re_sq_le_integral_norm_bigF_sq (Z := Z) (m := m)
    h psi hb.orthonormal
  have hmoment := sum_testKernel_sq_re_eq_integral_norm_bigF_sq h hZ
  have hcardNat : (simpleRealPart Z m).card + (multipleRealPart Z m).card
        + (nonRealPart Z).card = Z.card := by
    rw [← Finset.card_union_of_disjoint disjoint_simpleRealPart_multipleRealPart,
      ← Finset.card_union_of_disjoint disjoint_realPart_nonRealPart,
      union_realPart_nonRealPart hZ]
  have hcard : ((simpleRealPart Z m).card : ℝ)
        + ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ)
      = (Z.card : ℝ) := by exact_mod_cast hcardNat
  change 3 * (∑ j, a j) -
      2 * (((simpleRealPart Z m).card : ℝ) +
        ((multipleRealPart Z m).card : ℝ) + ((nonRealPart Z).card : ℝ))
      ≤ ∑ j, a j ^ 2 at hrange
  change ∑ j, a j ^ 2 ≤ _ at hbessel
  rw [← hmoment] at hbessel
  linarith

end ZetaZeros
