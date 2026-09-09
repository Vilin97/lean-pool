/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.JetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryODE

@[expose] public section

/-!
# Uniform slow jets of the actual phase geometry

The index type below carries the band, representative, and rounded frequency.
It is not a differentiation variable.  All derivatives are actual Fréchet
derivatives in the slow variables (and, when present, the slot variable).
-/

noncomputable section

namespace NavierStokes.PhaseJetBounds

open Set
open scoped Topology ContDiff InnerProductSpace

/-- A family of open chart domains, with a slow scale at least one. -/
structure Domain (ι E : Type*) [NormedAddCommGroup E] where
  scale : ι → ℝ
  carrier : ι → Set E
  isOpen : ∀ i, IsOpen (carrier i)
  one_le_scale : ∀ i, 1 ≤ scale i

/-- Every fixed finite collection of actual derivatives has one polynomial
bound, uniform over all bands and charts in the index type. -/
structure PolynomialJets {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : Domain ι E) (f : ι → E → F) : Prop where
  smooth : ∀ i, ContDiffOn ℝ ∞ (f i) (D.carrier i)
  bound : ∀ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∃ m : ℕ,
    ∀ i, JetBounds.FiniteJetBound N (f i) (D.carrier i) (C * D.scale i ^ m)

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl n

private theorem one_le_mul' {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  nlinarith

section Calculus

variable {ι E F G H : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Domain ι E}

theorem PolynomialJets.congr {f g : ι → E → F} (hf : PolynomialJets D f)
    (hfg : ∀ i, EqOn (f i) (g i) (D.carrier i)) : PolynomialJets D g := by
  refine ⟨fun i => (hf.smooth i).congr (fun x hx => (hfg i hx).symm), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C, hC, m, ?_⟩
  intro i n hn x hx
  have he := iteratedFDerivWithin_congr (𝕜 := ℝ) (hfg i) hx n
  rw [iteratedFDerivWithin_of_isOpen n (D.isOpen i) hx,
    iteratedFDerivWithin_of_isOpen n (D.isOpen i) hx] at he
  rw [← he]
  exact hm i n hn x hx

theorem PolynomialJets.const (c : ι → F) {C : ℝ} {m : ℕ} (hC : 1 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ C * D.scale i ^ m) :
    PolynomialJets D (fun i _ => c i) := by
  refine ⟨fun _ => contDiffOn_const, fun _ => ⟨C, hC, m, ?_⟩⟩
  intro i n hn x hx
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hc i
  | succ n =>
      rw [iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg (le_trans zero_le_one hC)
        (pow_nonneg (le_trans zero_le_one (D.one_le_scale i)) _)

theorem PolynomialJets.const_uniform (c : ι → F) {C : ℝ} (hC : 1 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ C) : PolynomialJets D (fun i _ => c i) :=
  PolynomialJets.const c hC (m := 0) (by simpa using hc)

theorem PolynomialJets.const_fixed (c : F) : PolynomialJets D (fun _ _ => c) :=
  PolynomialJets.const_uniform _ (le_max_left 1 ‖c‖) (fun _ => le_max_right _ _)

theorem PolynomialJets.clm {f : ι → E → F} (hf : PolynomialJets D f)
    (L : F →L[ℝ] G) : PolynomialJets D (fun i x => L (f i x)) := by
  refine ⟨fun i => L.contDiff.comp_contDiffOn (hf.smooth i), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨(‖L‖ + 1) * C, ?_, m, ?_⟩
  · nlinarith [norm_nonneg L]
  intro i n hn x hx
  have he := L.iteratedFDeriv_comp_left
    ((hf.smooth i).contDiffAt ((D.isOpen i).mem_nhds hx)) (nat_le_infty n)
  change ‖iteratedFDeriv ℝ n (L ∘ f i) x‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n (f i) x‖ := L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L‖ * (C * D.scale i ^ m) :=
      mul_le_mul_of_nonneg_left (hm i n hn x hx) (norm_nonneg L)
    _ ≤ (‖L‖ + 1) * C * D.scale i ^ m := by
      have := pow_nonneg (le_trans zero_le_one (D.one_le_scale i)) m
      nlinarith

theorem PolynomialJets.add {f g : ι → E → F}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => f i x + g i x) := by
  refine ⟨fun i => (hf.smooth i).add (hg.smooth i), ?_⟩
  intro N
  obtain ⟨A, hA, a, ha⟩ := hf.bound N
  obtain ⟨B, hB, b, hb⟩ := hg.bound N
  refine ⟨A + B, by linarith, a + b, ?_⟩
  intro i
  apply (JetBounds.FiniteJetBound.add (D.isOpen i)
    ((hf.smooth i).of_le (nat_le_infty N)) ((hg.smooth i).of_le (nat_le_infty N))
    (ha i) (hb i)).mono
  have hsa := pow_le_pow_right₀ (D.one_le_scale i) (Nat.le_add_right a b)
  have hsb := pow_le_pow_right₀ (D.one_le_scale i) (Nat.le_add_left b a)
  nlinarith

theorem PolynomialJets.neg {f : ι → E → F} (hf : PolynomialJets D f) :
    PolynomialJets D (fun i x => -f i x) := by
  simpa using hf.clm (-ContinuousLinearMap.id ℝ F)

theorem PolynomialJets.sub {f g : ι → E → F}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => f i x - g i x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem PolynomialJets.pair {f : ι → E → F} {g : ι → E → G}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => (f i x, g i x)) := by
  simpa using (hf.clm (ContinuousLinearMap.inl ℝ F G)).add
    (hg.clm (ContinuousLinearMap.inr ℝ F G))

theorem PolynomialJets.bilinear {f : ι → E → F} {g : ι → E → G}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g)
    (B : F →L[ℝ] G →L[ℝ] H) :
    PolynomialJets D (fun i x => B (f i x) (g i x)) := by
  refine ⟨fun i => B.isBoundedBilinearMap.contDiff.comp_contDiffOn
    ((hf.smooth i).prodMk (hg.smooth i)), ?_⟩
  intro N
  obtain ⟨A, hA, a, ha⟩ := hf.bound N
  obtain ⟨C, hC, c, hc⟩ := hg.bound N
  refine ⟨(‖B‖ + 1) * 2 ^ N * A * C, ?_, a + c, ?_⟩
  · have hpow : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    have hba : 1 ≤ (‖B‖ + 1) * 2 ^ N := one_le_mul' (by nlinarith [norm_nonneg B]) hpow
    exact one_le_mul' (one_le_mul' hba hA) hC
  intro i
  apply (JetBounds.FiniteJetBound.bilinear B (D.isOpen i)
    ((hf.smooth i).of_le (nat_le_infty N)) ((hg.smooth i).of_le (nat_le_infty N))
    (ha i) (hc i)).mono
  rw [pow_add]
  have hs := le_trans zero_le_one (D.one_le_scale i)
  have ha0 : 0 ≤ A := le_trans zero_le_one hA
  have hc0 : 0 ≤ C := le_trans zero_le_one hC
  nlinarith [mul_nonneg (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) N)
    (mul_nonneg (mul_nonneg ha0 hc0) (mul_nonneg (pow_nonneg hs a) (pow_nonneg hs c)))]

theorem PolynomialJets.mul {f g : ι → E → ℝ}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => f i x * g i x) := by
  simpa using hf.bilinear hg (ContinuousLinearMap.mul ℝ ℝ)

theorem PolynomialJets.smul {f : ι → E → ℝ} {g : ι → E → F}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => f i x • g i x) := by
  simpa using hf.bilinear hg (ContinuousLinearMap.lsmul ℝ ℝ)

theorem PolynomialJets.fderiv {f : ι → E → F} (hf : PolynomialJets D f) :
    PolynomialJets D (fun i => fderiv ℝ (f i)) := by
  refine ⟨fun i => (hf.smooth i).fderiv_of_isOpen (D.isOpen i) (by simp), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound (N + 1)
  exact ⟨C, hC, m, fun i => (hm i).fderiv⟩

theorem PolynomialJets.directional {f : ι → E → F} (hf : PolynomialJets D f) (v : E) :
    PolynomialJets D (fun i x => _root_.fderiv ℝ (f i) x v) :=
  hf.fderiv.clm (ContinuousLinearMap.apply ℝ F v)

/-- Affine coordinates have only a zeroth and first derivative. -/
theorem PolynomialJets.affine (L : E →L[ℝ] F) (c : ι → F) {C : ℝ} {m : ℕ}
    (hC : 1 ≤ C) (hv : ∀ i, ∀ x ∈ D.carrier i, ‖L x + c i‖ ≤ C * D.scale i ^ m) :
    PolynomialJets D (fun i x => L x + c i) := by
  refine ⟨fun _ => L.contDiff.contDiffOn.add contDiffOn_const, ?_⟩
  intro N
  refine ⟨C + ‖L‖, by nlinarith [norm_nonneg L], m, ?_⟩
  intro i n hn x hx
  have hs : 1 ≤ D.scale i ^ m := one_le_pow₀ (D.one_le_scale i)
  have hfd : _root_.fderiv ℝ (fun y => L y + c i) = fun _ => L := by
    funext y
    exact (L.hasFDerivAt.add_const (c i)).fderiv
  cases n with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact (hv i x hx).trans (by nlinarith [norm_nonneg L])
  | succ n =>
      rw [← norm_iteratedFDeriv_fderiv, hfd]
      cases n with
      | zero =>
          rw [norm_iteratedFDeriv_zero]
          nlinarith [norm_nonneg L]
      | succ n =>
          rw [iteratedFDeriv_succ_const]
          simp only [Pi.zero_apply, norm_zero]
          positivity

theorem norm_jet_comp_linear {f : F → G} {U : Set F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (L : E →L[ℝ] F) {x : E} (hx : L x ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ * ‖L‖ ^ n := by
  have hp := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hp.uniqueDiffOn hx
    (i := n) (nat_le_infty n)
  rw [iteratedFDerivWithin_of_isOpen n hp hx,
    iteratedFDerivWithin_of_isOpen n hU hx] at he
  rw [he]
  simpa using (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

/-- Translations introduce no growth in higher-derivative norms. -/
theorem norm_jet_comp_affine {f : F → G} {U : Set F}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (L : E →L[ℝ] F) (c : F) {x : E} (hx : L x + c ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f (L y + c)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (L x + c)‖ * ‖L‖ ^ n := by
  let g := fun y => f (y + c)
  have hs : IsOpen ((fun y : F => y + c) ⁻¹' U) := hU.preimage (continuous_id.add continuous_const)
  have hg : ContDiffOn ℝ ∞ g ((fun y : F => y + c) ⁻¹' U) :=
    hf.comp (contDiffOn_id.add contDiffOn_const) (fun _ hy => hy)
  have he := norm_jet_comp_linear hs hg L hx n
  simpa only [g, Function.comp_def, iteratedFDeriv_comp_add_right] using he

theorem PolynomialJets.precomp_affine {D' : Domain ι F} {f : ι → F → G}
    (hf : PolynomialJets D' f) (L : E →L[ℝ] F) (c : ι → F)
    (hscale : ∀ i, D'.scale i = D.scale i)
    (hmap : ∀ i, ∀ x ∈ D.carrier i, L x + c i ∈ D'.carrier i) :
    PolynomialJets D (fun i x => f i (L x + c i)) := by
  refine ⟨fun i => (hf.smooth i).comp
    (L.contDiff.contDiffOn.add contDiffOn_const) (hmap i), ?_⟩
  intro N
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  refine ⟨C * (‖L‖ + 1) ^ N, one_le_mul' hC (one_le_pow₀ (by nlinarith [norm_nonneg L])), m, ?_⟩
  intro i n hn x hx
  have hp : ‖L‖ ^ n ≤ (‖L‖ + 1) ^ N :=
    (pow_le_pow_left₀ (norm_nonneg L) (by linarith) n).trans
      (pow_le_pow_right₀ (by nlinarith [norm_nonneg L]) hn)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (f i) (L x + c i)‖ * ‖L‖ ^ n :=
      norm_jet_comp_affine (D'.isOpen i) (hf.smooth i) L (c i) (hmap i x hx) n
    _ ≤ (C * D'.scale i ^ m) * (‖L‖ + 1) ^ N :=
      mul_le_mul (hm i n hn _ (hmap i x hx)) hp (by positivity)
        (by have := le_trans zero_le_one (D'.one_le_scale i); positivity)
    _ = _ := by rw [hscale]; ring

theorem compact_jet_bound {g : F → G} {U K : Set F}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (hK : IsCompact K) (hKU : K ⊆ U)
    (N : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ JetBounds.FiniteJetBound N g K C := by
  have hsingle (k : ℕ) : ∃ C : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ k g y‖ ≤ C := by
    have hc := (hg.continuousOn_iteratedFDerivWithin
      (m := k) (nat_le_infty k) hU.uniqueDiffOn).mono hKU
    have he : ContinuousOn (iteratedFDeriv ℝ k g) K := by
      apply hc.congr
      intro y hy
      exact (iteratedFDerivWithin_of_isOpen k hU (hKU hy)).symm
    exact hK.exists_bound_of_continuousOn he
  induction N with
  | zero =>
      obtain ⟨C, hC⟩ := hsingle 0
      refine ⟨max 1 C, le_max_left _ _, ?_⟩
      intro k hk y hy
      have : k = 0 := by omega
      subst k
      exact (hC y hy).trans (le_max_right _ _)
  | succ N ih =>
      obtain ⟨C, hC, hc⟩ := ih
      obtain ⟨B, hB⟩ := hsingle (N + 1)
      refine ⟨max C B, hC.trans (le_max_left _ _), ?_⟩
      intro k hk y hy
      by_cases hkN : k ≤ N
      · exact (hc k hkN y hy).trans (le_max_left _ _)
      · have : k = N + 1 := by omega
        subst k
        exact (hB y hy).trans (le_max_right _ _)

/-- The higher chain rule is quantitative: compactness is applied only to the
fixed outer function, never to the varying band or to its derivatives. -/
theorem PolynomialJets.compact_comp {f : ι → E → F} (hf : PolynomialJets D f)
    {g : F → G} {U K : Set F} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hmap : ∀ i, MapsTo (f i) (D.carrier i) K) :
    PolynomialJets D (fun i x => g (f i x)) := by
  have hmapU (i) : MapsTo (f i) (D.carrier i) U := fun x hx => hKU (hmap i hx)
  refine ⟨fun i => hg.comp (hf.smooth i) (hmapU i), ?_⟩
  intro N
  obtain ⟨A, hA, m, ha⟩ := hf.bound N
  obtain ⟨C, hC, hc⟩ := compact_jet_bound hU hg hK hKU N
  refine ⟨(N.factorial : ℝ) * C * A ^ N, ?_, m * N, ?_⟩
  · have hfac : (1 : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
    exact one_le_mul' (one_le_mul' hfac hC) (one_le_pow₀ hA)
  intro i n hn x hx
  have hs : 1 ≤ D.scale i ^ m := one_le_pow₀ (D.one_le_scale i)
  have hD : 1 ≤ A * D.scale i ^ m := one_le_mul' hA hs
  have h := norm_iteratedFDerivWithin_comp_le hg (hf.smooth i) (nat_le_infty n)
    hU.uniqueDiffOn (D.isOpen i).uniqueDiffOn (hmapU i) hx
    (C := C) (D := A * D.scale i ^ m) (fun k hk => ?_) (fun k hk hkn => ?_)
  · rw [iteratedFDerivWithin_of_isOpen n (D.isOpen i) hx] at h
    change ‖iteratedFDeriv ℝ n (g ∘ f i) x‖ ≤ _
    calc
      _ ≤ (n.factorial : ℝ) * C * (A * D.scale i ^ m) ^ n := h
      _ ≤ (N.factorial : ℝ) * C * (A * D.scale i ^ m) ^ N := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.factorial_le hn) (le_trans zero_le_one hC)
        · exact pow_le_pow_right₀ hD hn
        · positivity
        · positivity
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  · rw [iteratedFDerivWithin_of_isOpen k hU (hmapU i hx)]
    exact hc k (hk.trans hn) (f i x) (hmap i hx)
  · rw [iteratedFDerivWithin_of_isOpen k (D.isOpen i) hx]
    exact (ha i k (hkn.trans hn) x hx).trans
      (by simpa using pow_le_pow_right₀ hD hk)

end Calculus

section Algebra

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {D : Domain ι E}

theorem PolynomialJets.inner {f g : ι → E → F}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => ⟪f i x, g i x⟫_ℝ) := by
  exact hf.bilinear hg (innerSL ℝ)

theorem PolynomialJets.norm_sq {f : ι → E → F} (hf : PolynomialJets D f) :
    PolynomialJets D (fun i x => ‖f i x‖ ^ 2) := by
  simpa only [real_inner_self_eq_norm_sq] using hf.inner hf

theorem PolynomialJets.pow {f : ι → E → ℝ} (hf : PolynomialJets D f) (n : ℕ) :
    PolynomialJets D (fun i x => f i x ^ n) := by
  induction n with
  | zero => simpa using (PolynomialJets.const_fixed (D := D) (1 : ℝ))
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem PolynomialJets.div_const {f : ι → E → ℝ} (hf : PolynomialJets D f) (c : ℝ) :
    PolynomialJets D (fun i x => f i x / c) := by
  simpa only [div_eq_mul_inv] using hf.mul (PolynomialJets.const_fixed c⁻¹)

/-- Inversion is used only on a uniformly separated compact range. -/
theorem PolynomialJets.inv {f : ι → E → ℝ} (hf : PolynomialJets D f)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ i, ∀ x ∈ D.carrier i, b ≤ |f i x|)
    (hupper : ∀ i, ∀ x ∈ D.carrier i, |f i x| ≤ M) :
    PolynomialJets D (fun i x => (f i x)⁻¹) := by
  let K : Set ℝ := Metric.closedBall 0 M ∩ {r | b ≤ |r|}
  have hK : IsCompact K := (isCompact_closedBall 0 M).inter_right
    (isClosed_le continuous_const continuous_abs)
  have hKU : K ⊆ {r : ℝ | r ≠ 0} := by
    intro r hr he
    have h : b ≤ |r| := hr.2
    simp only [he, abs_zero] at h
    linarith
  apply hf.compact_comp (isClosed_singleton.isOpen_compl)
    (contDiffOn_id.inv (fun _ h => h)) hK hKU
  intro i x hx
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hupper i x
    hx,
    hlower i x hx⟩

end Algebra

abbrev Plane := MovingFrameODE.Plane
abbrev Space := MovingFrameODE.Space
abbrev Slow := PhaseCalculus.Slow

def regularNormals : Set Space := {n | MovingFrameODE.tail n ≠ 0}

def normalRange (b M : ℝ) : Set Space :=
  Metric.closedBall 0 M ∩ {n | b ≤ ‖MovingFrameODE.tail n‖}

theorem regularNormals_isOpen : IsOpen regularNormals :=
  isClosed_singleton.isOpen_compl.preimage MovingFrameODE.tailCLM.continuous

theorem normalRange_isCompact (b M : ℝ) : IsCompact (normalRange b M) :=
  (isCompact_closedBall 0 M).inter_right
    (isClosed_le continuous_const MovingFrameODE.tailCLM.continuous.norm)

theorem normalRange_regular {b M : ℝ} (hb : 0 < b) : normalRange b M ⊆ regularNormals := by
  intro n hn he
  have h : b ≤ ‖MovingFrameODE.tail n‖ := hn.2
  simp only [he, norm_zero] at h
  linarith

section Geometry

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {D : Domain ι E} {n nDot : ι → E → Space}

/-- All normalized geometric quantities needed in the moving-frame ODE.
Their jets are conclusions of `normalGeometry_jets`, not assumptions there. -/
structure NormalGeometryJets (D : Domain ι E) (n nDot : ι → E → Space) : Prop where
  scale : PolynomialJets D (fun i x => MovingFrameODE.normalScale (n i x))
  invScale : PolynomialJets D (fun i x => (MovingFrameODE.normalScale (n i x))⁻¹)
  rho : PolynomialJets D (fun i x => MovingFrameODE.radialSlope (n i x))
  invDenom : PolynomialJets D (fun i x => (1 + MovingFrameODE.radialSlope (n i x) ^ 2)⁻¹)
  K : PolynomialJets D (fun i x => MovingFrameODE.normalDirection (n i x))
  N : PolynomialJets D (fun i x => MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n i
    x)))
  betaDot : PolynomialJets D (fun i x => PhaseEstimates.scaleDerivative (n i x) (nDot i x))
  rhoDot : PolynomialJets D (fun i x => PhaseEstimates.slopeDerivative (n i x) (nDot i x))
  directionDot : PolynomialJets D (fun i x => PhaseEstimates.directionDerivative (n i x) (nDot i x))
  rotation : PolynomialJets D (fun i x => PhaseEstimates.angularVelocity (n i x) (nDot i x))

theorem normalGeometry_jets (hn : PolynomialJets D n) (hd : PolynomialJets D nDot)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ i, ∀ x ∈ D.carrier i, b ≤ ‖MovingFrameODE.tail (n i x)‖)
    (hupper : ∀ i, ∀ x ∈ D.carrier i, ‖n i x‖ ≤ M) :
    NormalGeometryJets D n nDot := by
  have hmap : ∀ i, MapsTo (n i) (D.carrier i) (normalRange b M) := by
    intro i x hx
    exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hupper i x hx,
      hlower i x hx⟩
  have hs : ContDiffOn ℝ ∞ MovingFrameODE.normalScale regularNormals := by
    intro z hz
    exact (MovingFrameODE.contDiffAt_normalScale contDiffAt_id hz).contDiffWithinAt
  have hr : ContDiffOn ℝ ∞ MovingFrameODE.radialSlope regularNormals := by
    intro z hz
    exact (MovingFrameODE.contDiffAt_radialSlope contDiffAt_id hz).contDiffWithinAt
  have hk : ContDiffOn ℝ ∞ MovingFrameODE.normalDirection regularNormals := by
    intro z hz
    exact (MovingFrameODE.contDiffAt_normalDirection contDiffAt_id hz).contDiffWithinAt
  have hsinv : ContDiffOn ℝ ∞ (fun z => (MovingFrameODE.normalScale z)⁻¹) regularNormals :=
    hs.inv (fun z hz => (MovingFrameODE.normalScale_pos hz).ne')
  have hdinv : ContDiffOn ℝ ∞ (fun z => (1 + MovingFrameODE.radialSlope z ^ 2)⁻¹)
      regularNormals := (contDiffOn_const.add (hr.pow 2)).inv (fun z _ => by positivity)
  have pscale := hn.compact_comp regularNormals_isOpen hs (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have pinv := hn.compact_comp regularNormals_isOpen hsinv (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have prho := hn.compact_comp regularNormals_isOpen hr (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have pdenom := hn.compact_comp regularNormals_isOpen hdinv (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have pk := hn.compact_comp regularNormals_isOpen hk (normalRange_isCompact b M)
    (normalRange_regular hb) hmap
  have pn := pk.clm MovingFrameODE.quarterTurn
  have pt : PolynomialJets D (fun i x => MovingFrameODE.tail (n i x)) := hn.clm
    MovingFrameODE.tailCLM
  have ptd : PolynomialJets D (fun i x => MovingFrameODE.tail (nDot i x)) := hd.clm
    MovingFrameODE.tailCLM
  have prd := hd.clm (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)
  have psd : PolynomialJets D (fun i x => PhaseEstimates.scaleDerivative (n i x) (nDot i x)) := by
    simpa only [PhaseEstimates.scaleDerivative, div_eq_mul_inv]
      using (pt.inner ptd).mul pinv
  have prhod : PolynomialJets D (fun i x => PhaseEstimates.slopeDerivative (n i x) (nDot i x)) := by
    simpa only [PhaseEstimates.slopeDerivative, PiLp.proj_apply, div_eq_mul_inv]
      using (prd.sub (prho.mul psd)).mul pinv
  have pkd : PolynomialJets D (fun i x => PhaseEstimates.directionDerivative (n i x) (nDot i x)) :=
    by
    simpa only [PhaseEstimates.directionDerivative]
      using pinv.smul (ptd.sub (psd.smul pk))
  exact ⟨pscale, pinv, prho, pdenom, pk, pn, psd, prhod, pkd, pn.inner pkd⟩

end Geometry

section Phase

variable {ι : Type*}

/-- Uniform normalized base-field jets are a sufficient input.  The bound is
on the base field itself, before any normal or frame is constructed. -/
theorem polynomialJets_of_uniform {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : Domain ι E} {f : ι → E → F}
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (D.carrier i))
    (hbound : ∀ N : ℕ, ∃ C : ℝ, 1 ≤ C ∧
      ∀ i, JetBounds.FiniteJetBound N (f i) (D.carrier i) C) : PolynomialJets D f := by
  refine ⟨hf, ?_⟩
  intro N
  obtain ⟨C, hC, hc⟩ := hbound N
  exact ⟨C, hC, 0, by simpa only [pow_zero, mul_one] using hc⟩

noncomputable def Domain.slot (D : Domain ι Slow) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i)) :
    Domain ι (Slow × ℝ) where
  scale := D.scale
  carrier i := D.carrier i ×ˢ V i
  isOpen i := (D.isOpen i).prod (hV i)
  one_le_scale := D.one_le_scale

theorem PolynomialJets.lift_slot {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : Domain ι Slow} {f : ι → Slow → F} (hf : PolynomialJets D f)
    (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i)) :
    PolynomialJets (D.slot V hV) (fun i z => f i z.1) := by
  simpa only [ContinuousLinearMap.coe_fst', add_zero] using
    hf.precomp_affine (D := D.slot V hV) (ContinuousLinearMap.fst ℝ Slow ℝ)
      (fun _ => 0) (fun _ => rfl) (fun _ _ hz => by simpa using hz.1)

theorem PolynomialJets.vec2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Domain ι E} {f g : ι → E → ℝ}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) :
    PolynomialJets D (fun i x => (!₂[f i x, g i x] : Plane)) :=
  (hf.pair hg).clm MovingFrameODE.pairCLM

theorem PolynomialJets.vec3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Domain ι E} {f g h : ι → E → ℝ}
    (hf : PolynomialJets D f) (hg : PolynomialJets D g) (hh : PolynomialJets D h) :
    PolynomialJets D (fun i x => (!₂[f i x, g i x, h i x] : Space)) :=
  (hf.pair (hg.vec2 hh)).clm MovingFrameODE.packCLM

/-- The explicit normal has polynomial jets.  No inverse power of epsilon
occurs in this formula, although it occurs in the phase itself. -/
theorem explicitNormal_polynomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Domain ι E} {ε p pz x0 R v FR GR FZ GZ : ι → E → ℝ}
    (hε : PolynomialJets D ε) (hp : PolynomialJets D p) (hpz : PolynomialJets D pz)
    (hx : PolynomialJets D x0) (hRi : PolynomialJets D (fun i x => (R i x)⁻¹))
    (hv : PolynomialJets D v) (hFR : PolynomialJets D FR) (hGR : PolynomialJets D GR)
    (hFZ : PolynomialJets D FZ) (hGZ : PolynomialJets D GZ) :
    PolynomialJets D (fun i z => PhaseEstimates.explicitNormal (ε i z) (p i z) (pz i z)
      (x0 i z) (R i z) (v i z) (FR i z) (GR i z) (FZ i z) (GZ i z)) := by
  simpa only [PhaseEstimates.explicitNormal, div_eq_mul_inv] using
    (hx.sub (hv.mul ((hp.mul hFR).add (hpz.mul hGR)))).vec3 (hp.mul hRi)
      (hpz.sub ((hε.mul hv).mul ((hp.mul hFZ).add (hpz.mul hGZ))))

theorem normalVelocity_polynomial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Domain ι E} {ε p pz FR GR FZ GZ : ι → E → ℝ}
    (hε : PolynomialJets D ε) (hp : PolynomialJets D p) (hpz : PolynomialJets D pz)
    (hFR : PolynomialJets D FR) (hGR : PolynomialJets D GR)
    (hFZ : PolynomialJets D FZ) (hGZ : PolynomialJets D GZ) :
    PolynomialJets D (fun i z => PhaseEstimates.normalVelocity (ε i z) (p i z) (pz i z)
      (FR i z) (GR i z) (FZ i z) (GZ i z)) := by
  simpa only [PhaseEstimates.normalVelocity, neg_mul] using
    ((hp.mul hFR).add (hpz.mul hGR)).neg.vec3 (PolynomialJets.const_fixed 0)
      (hε.mul ((hp.mul hFZ).add (hpz.mul hGZ))).neg

/-- Discrete label data.  In particular, `p` is held fixed when a jet is taken;
it may be the nonzero rounded frequency from `PhaseEstimates`. -/
structure PhaseFamily (ι : Type*) where
  epsilon : ι → ℝ
  p : ι → ℝ
  pz : ι → ℝ
  x0 : ι → ℝ
  theta : ι → ℝ
  F : ι → Slow → ℝ
  G : ι → Slow → ℝ

noncomputable def PhaseFamily.normal (a : PhaseFamily ι) (i : ι) (z : Slow × ℝ) : Space :=
  PhaseCalculus.phaseNormal (a.epsilon i) (a.p i) (a.pz i) (a.x0 i) (a.F i) (a.G i)
    (z.1, (a.theta i, z.2))

noncomputable def PhaseFamily.velocity (a : PhaseFamily ι) (i : ι) (z : Slow × ℝ) : Space :=
  PhaseCalculus.normalSlotDerivative (a.epsilon i) (a.p i) (a.pz i) (a.F i) (a.G i) z.1

noncomputable def PhaseFamily.shear (a : PhaseFamily ι) (i : ι) (z : Slow × ℝ) : Plane :=
  PhaseEstimates.shearVector (a.F i) (a.G i) z.1

/-- Actual phase-normal and shear jets derived from the base fields.  The
slot can have length of order S; the cylindrical radius stays in an annulus.
No derivatives of the normal, frame, or ODE coefficients are inputs. -/
theorem PhaseFamily.polynomial_jets (a : PhaseFamily ι) (D : Domain ι Slow)
    (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (hF : PolynomialJets D a.F) (hG : PolynomialJets D a.G)
    {r M : ℝ} (hr : 0 < r) (hM : 1 ≤ M)
    (hconstant : ∀ i, |a.epsilon i| ≤ M ∧ |a.p i| ≤ M ∧ |a.pz i| ≤ M ∧ |a.x0 i| ≤ M)
    (heps : ∀ i, a.epsilon i ≠ 0)
    (hR : ∀ i, ∀ q ∈ D.carrier i, r ≤ |q.1| ∧ |q.1| ≤ M)
    (hslot : ∀ i, ∀ v ∈ V i, |v| ≤ M * D.scale i) :
    PolynomialJets (D.slot V hV) a.normal ∧
      PolynomialJets (D.slot V hV) a.velocity ∧
      PolynomialJets (D.slot V hV) a.shear := by
  have hpε : PolynomialJets (D.slot V hV) (fun i _ => a.epsilon i) :=
    PolynomialJets.const_uniform _ hM (fun i => by simpa using (hconstant i).1)
  have hpp : PolynomialJets (D.slot V hV) (fun i _ => a.p i) :=
    PolynomialJets.const_uniform _ hM (fun i => by simpa using (hconstant i).2.1)
  have hppz : PolynomialJets (D.slot V hV) (fun i _ => a.pz i) :=
    PolynomialJets.const_uniform _ hM (fun i => by simpa using (hconstant i).2.2.1)
  have hpx : PolynomialJets (D.slot V hV) (fun i _ => a.x0 i) :=
    PolynomialJets.const_uniform _ hM (fun i => by simpa using (hconstant i).2.2.2)
  have hpR : PolynomialJets D (fun _ q => q.1) := by
    simpa only [ContinuousLinearMap.coe_fst', add_zero] using
      (PolynomialJets.affine (D := D) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
        (fun _ => 0) (m := 0) hM (fun i q hq => by simpa using (hR i q hq).2))
  have hpRi := (hpR.inv hr (fun i q hq => (hR i q hq).1)
    (fun i q hq => (hR i q hq).2)).lift_slot V hV
  have hpv : PolynomialJets (D.slot V hV) (fun _ z => z.2) := by
    simpa only [ContinuousLinearMap.coe_snd', add_zero] using
      (PolynomialJets.affine (D := D.slot V hV) (ContinuousLinearMap.snd ℝ Slow ℝ)
        (fun _ => 0) (m := 1) hM (fun i z hz => by simpa [Domain.slot] using hslot i z.2 hz.2))
  have hFR := (hF.directional (1, (0, 0))).lift_slot V hV
  have hGR := (hG.directional (1, (0, 0))).lift_slot V hV
  have hFZ := (hF.directional (0, (1, 0))).lift_slot V hV
  have hGZ := (hG.directional (0, (1, 0))).lift_slot V hV
  have hexp := explicitNormal_polynomial hpε hpp hppz hpx hpRi hpv hFR hGR hFZ hGZ
  have hn : PolynomialJets (D.slot V hV) a.normal := by
    apply hexp.congr
    intro i z hz
    exact (PhaseEstimates.phaseNormal_eq_explicit (a.epsilon i) (a.p i) (a.pz i) (a.x0 i)
      (a.F i) (a.G i) (z.1, (a.theta i, z.2)) (heps i)
      (((hF.smooth i).contDiffAt ((D.isOpen i).mem_nhds hz.1)).differentiableAt (by simp))
      (((hG.smooth i).contDiffAt ((D.isOpen i).mem_nhds hz.1)).differentiableAt (by simp))).symm
  have hd : PolynomialJets (D.slot V hV) a.velocity :=
    normalVelocity_polynomial hpε hpp hppz hFR hGR hFZ hGZ
  have hg : PolynomialJets (D.slot V hV) a.shear :=
    ((hpR.lift_slot V hV).mul hFR).vec2 hGR
  exact ⟨hn, hd, hg⟩

end Phase

section Coefficients

variable {ι : Type*} {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable {D : Domain ι (Q × ℝ)}

/-- Intermediate algebraic data used to assemble the *defined* modal
coefficient.  `frameJets_ofNormalLocal` proves these from phase-normal jets. -/
structure FrameJets (D : Domain ι (Q × ℝ)) (d : ι → PrimaryODE.FrameData Q) : Prop where
  beta : PolynomialJets D (fun i => (d i).beta)
  betaDot : PolynomialJets D (fun i => (d i).betaDot)
  rho : PolynomialJets D (fun i => (d i).rho)
  rhoDot : PolynomialJets D (fun i => (d i).rhoDot)
  rotation : PolynomialJets D (fun i => (d i).rotation)
  F : PolynomialJets D (fun i => (d i).F)
  shear : PolynomialJets D (fun i => (d i).shear)
  K : PolynomialJets D (fun i z => (d i).frame z 0)
  N : PolynomialJets D (fun i z => (d i).frame z 1)
  invDenom : PolynomialJets D (fun i z => (1 + (d i).rho z ^ 2)⁻¹)
  eigenvalue : PolynomialJets D (fun i => (d i).eigenvalue)
  eigenvector : PolynomialJets D (fun i => (d i).eigenvector)
  invEigenvector : PolynomialJets D (fun i z => ((d i).eigenvector z)⁻¹)
  eigenRate : PolynomialJets D (fun i => (d i).eigenRate)
  viscosity : PolynomialJets D (fun i => (d i).viscosity)
  eigenvector_ne_zero : ∀ i, ∀ z ∈ D.carrier i, (d i).eigenvector z ≠ 0

theorem FrameJets.smoothOn {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) (i : ι) :
    (d i).SmoothOn (D.carrier i) := by
  refine ⟨h.beta.smooth i, h.betaDot.smooth i, h.rho.smooth i, h.rhoDot.smooth i,
    h.rotation.smooth i, h.F.smooth i, h.shear.smooth i, ?_, h.eigenvalue.smooth i,
    h.eigenvector.smooth i, h.eigenRate.smooth i, h.viscosity.smooth i, h.eigenvector_ne_zero i⟩
  intro k
  fin_cases k
  · exact h.K.smooth i
  · exact h.N.smooth i

theorem FrameJets.errorA {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) :
    PolynomialJets D (fun i => (d i).errorA) := by
  unfold PrimaryODE.FrameData.errorA
  simpa only [PrimaryODE.FrameData.errorA, MovingFrameODE.coeff11, div_eq_mul_inv] using
    (h.rho.mul ((h.K.inner h.shear).sub h.rhoDot)).mul h.invDenom

theorem FrameJets.errorB {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) :
    PolynomialJets D (fun i => (d i).errorB) := by
  have hNt := h.N.clm (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)
  unfold PrimaryODE.FrameData.errorB
  simpa only [PrimaryODE.FrameData.errorB, MovingFrameODE.coeff12,
    PiLp.proj_apply, div_eq_mul_inv] using
    ((((PolynomialJets.const_fixed (D := D) (2 : ℝ)).mul h.F).mul hNt).sub
      (h.rho.mul h.rotation)).mul h.invDenom |>.sub (h.eigenvalue.mul h.invEigenvector)

theorem FrameJets.errorC {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) :
    PolynomialJets D (fun i => (d i).errorC) := by
  have hNt := h.N.clm (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)
  unfold PrimaryODE.FrameData.errorC
  simpa only [PrimaryODE.FrameData.errorC, MovingFrameODE.coeff21, PiLp.proj_apply] using
    (((((PolynomialJets.const_fixed (D := D) (2 : ℝ)).mul h.F).mul hNt).add
      (h.N.inner h.shear)).neg.add (h.rho.mul h.rotation)).sub
        (h.eigenvalue.mul h.eigenvector)

theorem FrameJets.modal_errors {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) :
    PolynomialJets D (fun i => (d i).error11) ∧
    PolynomialJets D (fun i => (d i).error12) ∧
    PolynomialJets D (fun i => (d i).error21) ∧
    PolynomialJets D (fun i => (d i).error22) := by
  have hb := h.eigenvector.mul h.errorB
  have hc := h.errorC.mul h.invEigenvector
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold PrimaryODE.FrameData.error11
    simpa only [PrimaryODE.FrameData.error11, MovingFrameODE.modal11, div_eq_mul_inv] using
      (((h.errorA.add hb).add hc).sub h.eigenRate).div_const 2
  · unfold PrimaryODE.FrameData.error12
    simpa only [PrimaryODE.FrameData.error12, MovingFrameODE.modal12, div_eq_mul_inv] using
      (((h.errorA.sub hb).add hc).add h.eigenRate).div_const 2
  · unfold PrimaryODE.FrameData.error21
    simpa only [PrimaryODE.FrameData.error21, MovingFrameODE.modal21, div_eq_mul_inv] using
      (((h.errorA.add hb).sub hc).add h.eigenRate).div_const 2
  · unfold PrimaryODE.FrameData.error22
    simpa only [PrimaryODE.FrameData.error22, MovingFrameODE.modal22, div_eq_mul_inv] using
      (((h.errorA.sub hb).sub hc).sub h.eigenRate).div_const 2

theorem FrameJets.coefficient {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d) (j : ℤ) :
    PolynomialJets D (fun i => (d i).coefficient j) := by
  obtain ⟨h11, h12, h21, h22⟩ := h.modal_errors
  have hd := (PolynomialJets.const_fixed (D := D) ((j : ℝ) ^ 2)).mul h.viscosity
  have hh := (((((h.eigenvalue.sub hd).add h11).smul
    (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 1 0 0 0))).add
      (h12.smul (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 0 1 0 0)))).add
        (h21.smul (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 0 0 1 0)))).add
          (((h.eigenvalue.neg.sub hd).add h22).smul
            (PolynomialJets.const_fixed (GrowingMode.modalOperator 0 0 0 0 0 1)))
  apply hh.congr
  intro i z _
  ext w k
  fin_cases k <;> simp [PrimaryODE.FrameData.coefficient, PrimaryODE.FrameData.damping,
    GrowingMode.modalOperator]

/-- The actual projection and eigenbasis conversion of a supplied source
preserve polynomial jets.  A scalar weight on the source can be carried
separately using linearity; no Gaussian source estimate is assumed here. -/
theorem FrameJets.forcing {d : ι → PrimaryODE.FrameData Q} (h : FrameJets D d)
    {f : ι → Q × ℝ → Space} (hf : PolynomialJets D f) :
    PolynomialJets D (fun i => (d i).forcing (f i)) := by
  have ht : PolynomialJets D (fun i x => MovingFrameODE.tail (f i x)) := hf.clm
    MovingFrameODE.tailCLM
  have hr := hf.clm (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)
  have hx : PolynomialJets D (fun i => (d i).forceX (f i)) := by
    unfold PrimaryODE.FrameData.forceX
    simpa only [PrimaryODE.FrameData.forceX, PiLp.proj_apply, div_eq_mul_inv] using
      ((hr.sub (h.rho.mul (h.K.inner ht))).neg.mul h.invDenom)
  have hy : PolynomialJets D (fun i => (d i).forceY (f i)) := (h.N.inner ht).neg
  have hdiv := hy.mul h.invEigenvector
  unfold PrimaryODE.FrameData.forcing
  simpa only [PrimaryODE.FrameData.forcing, div_eq_mul_inv] using
    ((hx.add hdiv).div_const 2).vec2 ((hx.sub hdiv).div_const 2)

/-- This theorem connects the proved normal estimates to the exact local
frame used by `PrimaryODE`, including normal motion and viscosity. -/
theorem frameJets_ofNormalLocal
    {n nDot : ι → Q × ℝ → Space} {F : ι → Q × ℝ → ℝ} {g : ι → Q × ℝ → Plane}
    {lam h rate ν : ι → Q × ℝ → ℝ}
    (hn : PolynomialJets D n) (hd : PolynomialJets D nDot)
    (hF : PolynomialJets D F) (hg : PolynomialJets D g)
    (hlam : PolynomialJets D lam) (hh : PolynomialJets D h)
    (hrate : PolynomialJets D rate) (hν : PolynomialJets D ν)
    {b M bh H : ℝ} (hb : 0 < b) (hbh : 0 < bh)
    (hnlow : ∀ i, ∀ z ∈ D.carrier i, b ≤ ‖MovingFrameODE.tail (n i z)‖)
    (hnup : ∀ i, ∀ z ∈ D.carrier i, ‖n i z‖ ≤ M)
    (hhlow : ∀ i, ∀ z ∈ D.carrier i, bh ≤ |h i z|)
    (hhup : ∀ i, ∀ z ∈ D.carrier i, |h i z| ≤ H) :
    FrameJets D (fun i => PrimaryODE.FrameData.ofNormalLocal
      (n i) (nDot i) (F i) (g i) (lam i) (h i) (rate i) (ν i)) := by
  have hgeom := normalGeometry_jets hn hd hb hnlow hnup
  have hne (i) (z) (hz : z ∈ D.carrier i) : MovingFrameODE.tail (n i z) ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le hb (hnlow i z hz))
  refine ⟨hgeom.scale, hgeom.betaDot, hgeom.rho, hgeom.rhoDot, hgeom.rotation, hF, hg,
    ?_, ?_, hgeom.invDenom, hlam, hh, hh.inv hbh hhlow hhup, hrate, hν.mul hn.norm_sq, ?_⟩
  · apply hgeom.K.congr
    intro i z hz
    simp only [PrimaryODE.FrameData.ofNormalLocal, PrimaryODE.localFrame_eq (hne i z hz),
      MovingFrameODE.normalFrame_zero]
  · apply hgeom.N.congr
    intro i z hz
    simp only [PrimaryODE.FrameData.ofNormalLocal, PrimaryODE.localFrame_eq (hne i z hz),
      MovingFrameODE.normalFrame_one]
  · intro i z hz he
    have hbnd := hhlow i z hz
    change h i z = 0 at he
    rw [he, abs_zero] at hbnd
    linarith

/-- The form consumed by `PrimaryODE.norm_iteratedFDeriv_solution_le_polynomial`
and `WeightedODEJets`: all parameter jets at fixed slot time share one
constant and one power of S.  The constant is independent of the slot time. -/
theorem PolynomialJets.parameter_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ι → Q × ℝ → F} (hf : PolynomialJets D f) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ m : ℕ, ∀ i p v, (p, v) ∈ D.carrier i →
      ∀ k ≤ N, ‖iteratedFDeriv ℝ k (fun q => f i (q, v)) p‖ ≤ C * D.scale i ^ m := by
  obtain ⟨C, hC, m, hm⟩ := hf.bound N
  let L := ContinuousLinearMap.inl ℝ Q ℝ
  refine ⟨C * (‖L‖ + 1) ^ N,
    one_le_mul' hC (one_le_pow₀ (by nlinarith [norm_nonneg L])), m, ?_⟩
  intro i p v hp k hk
  have hmap : L p + (0, v) ∈ D.carrier i := by simpa [L] using hp
  have hjet := norm_jet_comp_affine (D.isOpen i) (hf.smooth i) L (0, v) hmap k
  have hfac : ‖L‖ ^ k ≤ (‖L‖ + 1) ^ N :=
    (pow_le_pow_left₀ (norm_nonneg L) (by linarith) k).trans
      (pow_le_pow_right₀ (by nlinarith [norm_nonneg L]) hk)
  calc
    _ ≤ ‖iteratedFDeriv ℝ k (f i) (p, v)‖ * ‖L‖ ^ k := by simpa [L] using hjet
    _ ≤ (C * D.scale i ^ m) * (‖L‖ + 1) ^ N :=
      mul_le_mul (hm i k hk (p, v) hp) hfac (by positivity)
        (by have := le_trans zero_le_one (D.one_le_scale i); positivity)
    _ = _ := by ring

end Coefficients

section ReferenceBounds

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {D : Domain ι E}

omit [NormedSpace ℝ E] in
/-- Quantitative compact-range inputs obtained from the actual normal
comparison proved in `PhaseEstimates`, with no lower bound assumed on n. -/
theorem normal_range_of_reference_close {n : ι → E → Space}
    (B : ι → ℝ) (K : ι → Plane) (s δ : ι → E → ℝ)
    {b M : ℝ} (hb : 0 < b) (hM : 1 ≤ M)
    (hB : ∀ i, 2 * b ≤ B i ∧ B i ≤ M) (hK : ∀ i, ‖K i‖ = 1)
    (hs : ∀ i, ∀ z ∈ D.carrier i, |s i z| ≤ M)
    (hδ : ∀ i, ∀ z ∈ D.carrier i, δ i z ≤ B i / 2)
    (hclose : ∀ i, ∀ z ∈ D.carrier i,
      ‖n i z - MovingFrameODE.pack (B i * s i z) (B i • K i)‖ ≤ δ i z) :
    (∀ i, ∀ z ∈ D.carrier i, b ≤ ‖MovingFrameODE.tail (n i z)‖) ∧
      (∀ i, ∀ z ∈ D.carrier i, ‖n i z‖ ≤ M ^ 2 + 3 * M) := by
  have hBpos (i) : 0 < B i := lt_of_lt_of_le (by linarith) (hB i).1
  constructor
  · intro i z hz
    have h := (PhaseEstimates.normal_lower_bounds (hBpos i) (hK i) (hδ i z hz) (hclose i z hz)).1
    change b ≤ MovingFrameODE.normalScale (n i z)
    linarith [(hB i).1]
  · intro i z hz
    have hc (k : Fin 2) : |K i k| ≤ 1 := by
      simpa only [Real.norm_eq_abs, hK i] using PiLp.norm_apply_le (K i) k
    have href : ‖MovingFrameODE.pack (B i * s i z) (B i • K i)‖ ≤ M ^ 2 + 2 * M := by
      have hh := PhaseEstimates.vec3_norm_le_sum (MovingFrameODE.pack (B i * s i z) (B i • K i))
      change ‖MovingFrameODE.pack (B i * s i z) (B i • K i)‖ ≤
        |B i * s i z| + |B i * K i 0| + |B i * K i 1| at hh
      simp only [abs_mul, abs_of_pos (hBpos i)] at hh
      have h1 := mul_le_mul (hB i).2 (hs i z hz) (abs_nonneg _) (by linarith : 0 ≤ M)
      have h2 := mul_le_mul (hB i).2 (hc 0) (abs_nonneg _) (by linarith : 0 ≤ M)
      have h3 := mul_le_mul (hB i).2 (hc 1) (abs_nonneg _) (by linarith : 0 ≤ M)
      nlinarith
    have hh := norm_sub_le_norm_sub_add_norm_sub (n i z)
      (MovingFrameODE.pack (B i * s i z) (B i • K i)) 0
    simp only [sub_zero] at hh
    linarith [hclose i z hz, hδ i z hz, (hB i).2]

theorem PolynomialJets.radius {s : ι → E → ℝ} (hs : PolynomialJets D s)
    {M : ℝ} (hbound : ∀ i, ∀ z ∈ D.carrier i, |s i z| ≤ M) :
    PolynomialJets D (fun i z => Real.sqrt (1 + s i z ^ 2)) ∧
      PolynomialJets D (fun i z => (Real.sqrt (1 + s i z ^ 2))⁻¹) ∧
      PolynomialJets D (fun i z => (1 + s i z ^ 2)⁻¹) := by
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ => Real.sqrt (1 + x ^ 2)) univ :=
    (contDiffOn_const.add (contDiffOn_id.pow 2)).sqrt (fun x _ => by positivity)
  have hgi := hg.inv (fun x _ => (Real.sqrt_pos.mpr (by positivity)).ne')
  have hgd : ContDiffOn ℝ ∞ (fun x : ℝ => (1 + x ^ 2)⁻¹) univ :=
    (contDiffOn_const.add (contDiffOn_id.pow 2)).inv (fun x _ => by positivity)
  have hmap : ∀ i, MapsTo (s i) (D.carrier i) (Metric.closedBall 0 M) := by
    intro i z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hbound i z hz
  exact ⟨hs.compact_comp isOpen_univ hg (isCompact_closedBall 0 M) (subset_univ _) hmap,
    hs.compact_comp isOpen_univ hgi (isCompact_closedBall 0 M) (subset_univ _) hmap,
    hs.compact_comp isOpen_univ hgd (isCompact_closedBall 0 M) (subset_univ _) hmap⟩

theorem radius_bounds (s : ℝ) : 1 ≤ Real.sqrt (1 + s ^ 2) ∧
    Real.sqrt (1 + s ^ 2) ≤ 1 + |s| := by
  have hpos := Real.sqrt_nonneg (1 + s ^ 2)
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + s ^ 2 by positivity)
  constructor <;> nlinarith [sq_nonneg s, sq_abs s, abs_nonneg s]

end ReferenceBounds

section ReferenceJets

variable {ι Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
variable {D : Domain ι (Q × ℝ)}

/-- The reference eigenbasis is also derived from its explicit formula.
The hypothesis on u/ell is the scale-normalized slot-length bound; all four
parameters are frozen within each label. -/
theorem reference_jets (lam c0 u ell : ι → ℝ)
    {M b : ℝ} (hM : 1 ≤ M) (hb : 0 < b)
    (hlam : ∀ i, |lam i| ≤ M) (hc : ∀ i, b ≤ |c0 i| ∧ |c0 i| ≤ M)
    (hu : ∀ i, |u i| ≤ M) (hrate : ∀ i, |u i / ell i| * D.scale i ≤ M)
    (hslot : ∀ i, ∀ z ∈ D.carrier i, |z.2| ≤ M * D.scale i) :
    PolynomialJets D (fun i z => ViscousPropagator.referenceEigenvalue (lam i) (u i) (ell i) z.2) ∧
    PolynomialJets D (fun i z => PrimaryODE.referenceProfile (c0 i) (u i) (ell i) z.2) ∧
    PolynomialJets D (fun i z => PrimaryODE.referenceProfileRate (u i) (ell i) z.2) ∧
    (∀ i, ∀ z ∈ D.carrier i, b ≤ |PrimaryODE.referenceProfile (c0 i) (u i) (ell i) z.2|) ∧
    (∀ i, ∀ z ∈ D.carrier i,
      |PrimaryODE.referenceProfile (c0 i) (u i) (ell i) z.2| ≤ M * (1 + M + M ^ 2)) := by
  have hq (i) : |u i / ell i| ≤ M := by
    nlinarith [hrate i, D.one_le_scale i, abs_nonneg (u i / ell i)]
  have pu := PolynomialJets.const_uniform (D := D) u hM (fun i => by simpa using hu i)
  have pq := PolynomialJets.const_uniform (D := D) (fun i => u i / ell i) hM
    (fun i => by simpa only [Real.norm_eq_abs] using hq i)
  have plam := PolynomialJets.const_uniform (D := D) lam hM (fun i => by simpa using hlam i)
  have pc := PolynomialJets.const_uniform (D := D) c0 hM (fun i => by simpa using (hc i).2)
  have pv : PolynomialJets D (fun _ z => z.2) := by
    simpa only [ContinuousLinearMap.coe_snd', add_zero] using
      (PolynomialJets.affine (D := D) (ContinuousLinearMap.snd ℝ Q ℝ)
        (fun _ => 0) (m := 1) hM (fun i z hz => by simpa using hslot i z hz))
  have heq (i) (z : Q × ℝ) : u i / 2 + (u i / ell i) * z.2 =
      PulseGrowth.slotMagnitude (u i) (ell i) z.2 := by
    unfold PulseGrowth.slotMagnitude
    ring
  have ps : PolynomialJets D (fun i z => PulseGrowth.slotMagnitude (u i) (ell i) z.2) :=
    ((pu.div_const 2).add (pq.mul pv)).congr (fun i z _ => heq i z)
  have hsb (i) (z : Q × ℝ) (hz : z ∈ D.carrier i) :
      |PulseGrowth.slotMagnitude (u i) (ell i) z.2| ≤ M + M ^ 2 := by
    rw [← heq i z]
    have h1 : |u i / 2| ≤ M := by rw [abs_div]; norm_num; linarith [hu i]
    have h2 : |(u i / ell i) * z.2| ≤ M ^ 2 := by
      rw [abs_mul]
      have hh := mul_le_mul_of_nonneg_left (hslot i z hz) (abs_nonneg (u i / ell i))
      have hh' := mul_le_mul_of_nonneg_right (hrate i) (show 0 ≤ M by linarith)
      nlinarith
    exact (abs_add_le _ _).trans (by linarith)
  obtain ⟨pr, pri, pdi⟩ := ps.radius hsb
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ViscousPropagator.referenceEigenvalue, div_eq_mul_inv] using plam.mul pri
  · exact pc.mul pr
  · simpa only [PrimaryODE.referenceProfileRate, div_eq_mul_inv] using (ps.mul pq).mul pdi
  · intro i z _
    have h := (radius_bounds (PulseGrowth.slotMagnitude (u i) (ell i) z.2)).1
    simp only [PrimaryODE.referenceProfile, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [(hc i).1, abs_nonneg (c0 i)]
  · intro i z hz
    have h := (radius_bounds (PulseGrowth.slotMagnitude (u i) (ell i) z.2)).2.trans
      (add_le_add_right (hsb i z hz) 1)
    simp only [PrimaryODE.referenceProfile, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hh := mul_le_mul (hc i).2 h (Real.sqrt_nonneg _) (show 0 ≤ M by linarith)
    nlinarith

end ReferenceJets

section Assembly

variable {ι : Type*}

/-- The actual phase-derived frame with the explicit reference eigenbasis.
Only the band/representative labels enter the frozen scalar choices. -/
noncomputable def PhaseFamily.frameData (a : PhaseFamily ι)
    (lam c0 u ell ν : ι → ℝ) (i : ι) : PrimaryODE.FrameData Slow :=
  PrimaryODE.FrameData.ofNormalLocal (a.normal i) (a.velocity i)
    (fun z => a.F i z.1) (a.shear i)
    (fun z => ViscousPropagator.referenceEigenvalue (lam i) (u i) (ell i) z.2)
    (fun z => PrimaryODE.referenceProfile (c0 i) (u i) (ell i) z.2)
    (fun z => PrimaryODE.referenceProfileRate (u i) (ell i) z.2)
    (fun _ => ν i)

/-- Assembly from actual base jets, frozen representative bounds, and the
zeroth-order phase comparison.  That comparison is the conclusion of
`PhaseEstimates.actual_phase_estimates`; smallness follows from its large-band
theorems.  The lower bound on the *actual* normal is derived inside this proof. -/
theorem PhaseFamily.frameData_jets_of_phase_comparison
    (a : PhaseFamily ι) (D : Domain ι Slow) (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (lam c0 u ell ν B : ι → ℝ) (K : ι → Plane) (s δ : ι → Slow × ℝ → ℝ)
    (hF : PolynomialJets D a.F) (hG : PolynomialJets D a.G)
    {r b M : ℝ} (hr : 0 < r) (hb : 0 < b) (hM : 1 ≤ M)
    (hconstant : ∀ i, |a.epsilon i| ≤ M ∧ |a.p i| ≤ M ∧ |a.pz i| ≤ M ∧ |a.x0 i| ≤ M)
    (heps : ∀ i, a.epsilon i ≠ 0)
    (hR : ∀ i, ∀ q ∈ D.carrier i, r ≤ |q.1| ∧ |q.1| ≤ M)
    (hslot : ∀ i, ∀ v ∈ V i, |v| ≤ M * D.scale i)
    (hlam : ∀ i, |lam i| ≤ M) (hc : ∀ i, b ≤ |c0 i| ∧ |c0 i| ≤ M)
    (hu : ∀ i, |u i| ≤ M) (hrate : ∀ i, |u i / ell i| * D.scale i ≤ M)
    (hν : ∀ i, |ν i| ≤ M)
    (hB : ∀ i, 2 * b ≤ B i ∧ B i ≤ M) (hK : ∀ i, ‖K i‖ = 1)
    (hs : ∀ i, ∀ z ∈ (D.slot V hV).carrier i, |s i z| ≤ M)
    (hδ : ∀ i, ∀ z ∈ (D.slot V hV).carrier i, δ i z ≤ B i / 2)
    (hclose : ∀ i, ∀ z ∈ (D.slot V hV).carrier i,
      ‖a.normal i z - MovingFrameODE.pack (B i * s i z) (B i • K i)‖ ≤ δ i z) :
    FrameJets (D.slot V hV) (a.frameData lam c0 u ell ν) := by
  obtain ⟨hn, hd, hg⟩ := a.polynomial_jets D V hV hF hG hr hM hconstant heps hR hslot
  obtain ⟨hnlow, hnup⟩ := normal_range_of_reference_close (D := D.slot V hV)
    B K s δ hb hM hB hK hs hδ hclose
  obtain ⟨hl, hh, hq, hhlow, hhup⟩ := reference_jets (D := D.slot V hV)
    lam c0 u ell hM hb hlam hc hu hrate (fun i z hz => hslot i z.2 hz.2)
  have hνj := PolynomialJets.const_uniform (D := D.slot V hV) ν hM
    (fun i => by simpa only [Real.norm_eq_abs] using hν i)
  exact frameJets_ofNormalLocal hn hd (hF.lift_slot V hV) hg hl hh hq hνj
    hb hb hnlow hnup hhlow hhup

/-- Direct output in the fixed-slot format used by the ODE jet theorem.
The coefficient is the actual `FrameData.coefficient`, not a comparison ODE. -/
theorem FrameJets.coefficient_parameter_bounds
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {D : Domain ι (Q × ℝ)} {d : ι → PrimaryODE.FrameData Q}
    (hd : FrameJets D d) (j : ℤ) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ m : ℕ, ∀ i p v, (p, v) ∈ D.carrier i →
      ∀ k ≤ N, ‖iteratedFDeriv ℝ k (fun q => (d i).coefficient j (q, v)) p‖ ≤
        C * D.scale i ^ m :=
  (hd.coefficient j).parameter_bound N

end Assembly

section BandChoices

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {D : Domain ι E}

/-- The genuine nonzero angular rounding preserves uniform boundedness.
It is constant in the chart variables even when it jumps across labels. -/
theorem rounded_frequency_jets (k target : ι → ℝ) {M : ℝ} (hM : 1 ≤ M)
    (hk : ∀ i, 1 ≤ k i) (ht : ∀ i, |target i| ≤ M) :
    PolynomialJets D (fun i _ => PhaseEstimates.roundedFrequency (k i) (target i)) := by
  apply PolynomialJets.const_uniform _ (show 1 ≤ M + 1 by linarith)
  intro i
  have hkpos : 0 < k i := lt_of_lt_of_le zero_lt_one (hk i)
  have herr := PhaseEstimates.roundedFrequency_error hkpos (target i)
  have hinv : 1 / k i ≤ 1 := (div_le_one hkpos).mpr (hk i)
  have hsum := abs_add_le (PhaseEstimates.roundedFrequency (k i) (target i) - target i) (target i)
  rw [sub_add_cancel] at hsum
  rw [Real.norm_eq_abs]
  linarith [ht i]

/-- With the actual carrier choice, the fundamental viscosity factor is a
uniformly bounded label constant.  Thus no factor k is lost in slow jets. -/
theorem band_viscosity_jets (band : ι → ℕ) (h : ℝ) (hh : 0 ≤ h) :
    PolynomialJets D (fun i _ => ChartScales.epsilon h (band i) *
      (ChartScales.carrier h (band i) : ℝ) ^ 2) := by
  apply PolynomialJets.const_uniform _ (by norm_num : (1 : ℝ) ≤ 4)
  intro i
  obtain ⟨hl, hu⟩ := ChartScales.carrier_viscosity_bounds h hh (band i)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hl)]
  exact hu

theorem band_epsilon_jets (band : ι → ℕ) (h : ℝ) (hh : 0 ≤ h) :
    PolynomialJets D (fun i _ => ChartScales.epsilon h (band i)) := by
  apply PolynomialJets.const_uniform _ (le_refl (1 : ℝ))
  intro i
  rw [Real.norm_eq_abs, abs_of_pos (ChartScales.epsilon_pos h (band i))]
  exact ChartScales.epsilon_le_one h hh (band i)

theorem band_rounded_frequency_jets (band : ι → ℕ) (h : ℝ) (target : ι → ℝ)
    {M : ℝ} (hM : 1 ≤ M) (ht : ∀ i, |target i| ≤ M) :
    PolynomialJets D (fun i _ => PhaseEstimates.roundedFrequency
      (ChartScales.carrier h (band i) : ℝ) (target i)) := by
  apply rounded_frequency_jets _ target hM _ ht
  intro i
  have hp : 0 < (ChartScales.carrier h (band i) : ℝ) :=
    Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h (band i))
  have hp' : 0 < ChartScales.carrier h (band i) := by exact_mod_cast hp
  exact_mod_cast hp'

/-- A direct domain constructor with the manuscript's S(n)=n². -/
noncomputable def Domain.ofBands (band : ι → ℕ) (hband : ∀ i, 1 ≤ band i)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) : Domain ι E where
  scale i := ChartScales.S (band i)
  carrier := U
  isOpen := hU
  one_le_scale i := by
    have h : (1 : ℝ) ≤ band i := by exact_mod_cast hband i
    dsimp [ChartScales.S]
    nlinarith

omit [NormedSpace ℝ E] in
/-- The reference logarithmic-rate input follows from a lower slot-length
bound.  In particular `ChartScales.slotLength_bounds` gives c=2r₀. -/
theorem normalized_slot_rate_le {S ell u c M : ℝ} (hS : 0 < S) (hc : 0 < c)
    (hell : c * S ≤ ell) (hu : |u| ≤ M) : |u / ell| * S ≤ M / c := by
  have hellpos : 0 < ell := lt_of_lt_of_le (mul_pos hc hS) hell
  have hM : 0 ≤ M := (abs_nonneg u).trans hu
  rw [abs_div, abs_of_pos hellpos]
  apply (le_div_iff₀ hc).mpr
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_le_iff₀ hellpos).mpr
  have h1 := mul_le_mul_of_nonneg_right hu (mul_nonneg hS.le hc.le)
  have h2 := mul_le_mul_of_nonneg_left hell hM
  nlinarith

end BandChoices

end NavierStokes.PhaseJetBounds
