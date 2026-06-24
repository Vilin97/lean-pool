/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.OSforGFF.GaussianField.Nuclear.DyninMityagin
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries

/-!
# Nuclear Spaces (Pietsch characterization)

Defines the standard `NuclearSpace` typeclass (Pietsch characterization) and
proves that the Dynin-Mityagin characterization (`DyninMityaginSpace`) implies it.

## Two notions of nuclearity

The `DyninMityaginSpace` typeclass uses the **Dynin-Mityagin**
characterization: a Schauder basis with polynomial growth/decay in seminorms.
This is strictly stronger than **Pietsch nuclearity** (seminorm nuclear
dominance) because it additionally requires the existence of a Schauder basis.

The converse (Pietsch → Dynin-Mityagin) holds only for nuclear Fréchet spaces
that already possess a Schauder basis (the Dynin-Mityagin theorem). We do not
formalize that direction since our applications (Schwartz spaces) obtain the
DM structure directly from the Hermite basis.

## Main definitions and results

- `NuclearSpace` — Pietsch characterization typeclass
- `exists_CLF_le_seminorm` — Hahn-Banach for continuous seminorms
- `DyninMityaginSpace.toNuclearSpace` — DM implies Pietsch

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Pietsch, "Nuclear Locally Convex Spaces" (1972)
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4
-/

noncomputable section

namespace GaussianField

open scoped NNReal

/-! ### Nuclear Space Definition (Pietsch) -/

/-- A locally convex topological vector space over ℝ is **nuclear** if for every
    continuous seminorm `p`, there exist continuous linear functionals `(fₙ : E →L[ℝ] ℝ)`
    and non-negative reals `(cₙ)` with `Σ cₙ < ∞`, and a continuous seminorm `q ≥ p`,
    such that:

    (1) `p(x) ≤ Σₙ ‖fₙ(x)‖ · cₙ` for all `x`
    (2) `‖fₙ(x)‖ ≤ q(x)` for all `x`, `n`

    This is Pietsch's characterization, equivalent to Grothendieck's definition that
    the canonical map `E_q → E_p` between seminorm completions is nuclear.
-/
class NuclearSpace (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop where
  nuclear_dominance : ∀ (p : Seminorm ℝ E), Continuous p →
    ∃ (q : Seminorm ℝ E), Continuous q ∧ (∀ x, p x ≤ q x) ∧
    ∃ (f : ℕ → (E →L[ℝ] ℝ)) (c : ℕ → ℝ),
      (∀ n, 0 ≤ c n) ∧
      Summable c ∧
      (∀ n x, ‖f n x‖ ≤ q x) ∧
      (∀ x, p x ≤ ∑' n, ‖f n x‖ * c n)

/-! ### Hahn-Banach for Continuous Seminorms -/

/-- **Hahn-Banach for continuous seminorms.**

For a continuous seminorm `q` and any vector `f`, there exists a continuous
linear functional `φ` attaining `q` at `f` and bounded by `q` everywhere.
-/
lemma exists_CLF_le_seminorm
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (q : Seminorm ℝ E) (hq : Continuous q) (f : E) :
    ∃ φ : E →L[ℝ] ℝ, φ f = q f ∧ ∀ x, |φ x| ≤ q x := by
  by_cases hf : f = 0
  · exact ⟨0, by simp [hf, map_zero], fun x => by simp⟩
  · -- Define linear functional on span {f} with value q(f) at f
    let f₀ : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton f (q f) hf
    -- Apply Hahn-Banach extension with N = q (sublinear)
    obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear f₀ q
      (fun c hc x => by -- positive homogeneity: q(c • x) = c * q(x) for c > 0
        rw [map_smul_eq_mul]; simp [abs_of_pos hc])
      (fun x y => map_add_le_add q x y) -- subadditivity
      (fun ⟨x, hx⟩ => by -- bound: f₀(x) ≤ q(x) for x ∈ span {f}
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [LinearPMap.mkSpanSingleton'_apply]
        simp only [smul_eq_mul]
        calc c * q f ≤ |c| * q f :=
              mul_le_mul_of_nonneg_right (le_abs_self c) (apply_nonneg q f)
          _ = q (c • f) := by rw [map_smul_eq_mul]; simp)
    -- g(f) = q(f)
    have hg_f : g f = q f := by
      have h := hg_ext ⟨f, Submodule.mem_span_singleton.mpr ⟨1, one_smul _ _⟩⟩
      simpa only [f₀, LinearPMap.mkSpanSingleton'_apply_self] using h
    -- |g(x)| ≤ q(x) from g(x) ≤ q(x) and g(-x) ≤ q(-x) = q(x)
    have hg_abs : ∀ x, |g x| ≤ q x := by
      intro x; rw [abs_le]
      constructor
      · have h1 := hg_le (-x)
        rw [map_neg, map_neg_eq_map] at h1
        linarith
      · exact hg_le x
    -- g is continuous: bounded by continuous seminorm, hence continuous at 0
    have hg_cont : Continuous g := by
      apply continuous_of_continuousAt_zero g.toAddMonoidHom
      rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
      intro ε hε
      have hqε : {x : E | q x < ε} ∈ nhds (0 : E) :=
        (hq.isOpen_preimage _ isOpen_Iio).mem_nhds (by simp [map_zero, hε])
      exact Filter.mem_of_superset hqε (fun x hx => by
        simp only [Real.dist_eq, sub_zero]
        exact (hg_abs x).trans_lt hx)
    exact ⟨⟨g, hg_cont⟩, hg_f, hg_abs⟩

/-! ### Helper Lemmas for the Bridge Proof -/

/-- Auxiliary: a finset sup of seminorms applied to a sequence with polynomial
growth in each seminorm has a uniform polynomial bound.

Given `p' : ι → Seminorm ℝ E` and a finite set `s`, if each `p' i` for `i ∈ s`
satisfies `p' i (x m) ≤ Cᵢ · (1+m)^{tᵢ}`, then `(s.sup p') (x m) ≤ D · (1+m)^S`
where `S = max tᵢ` and `D = ∑ Cᵢ`.
-/
lemma finset_sup_poly_bound {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*}
    (p' : ι → Seminorm ℝ E) (s : Finset ι) (x : ℕ → E)
    (hx : ∀ i ∈ s, ∃ C > 0, ∃ t : ℕ, ∀ m, p' i (x m) ≤ C * (1 + (m : ℝ)) ^ t) :
    ∃ D > 0, ∃ S : ℕ, ∀ m, (s.sup p') (x m) ≤ D * (1 + (m : ℝ)) ^ S := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    exact ⟨1, one_pos, 0, fun m => by simp [Finset.sup_empty, Seminorm.bot_eq_zero]⟩
  | cons a s has ih =>
    have ih' := ih (fun i hi => hx i (Finset.mem_cons.mpr (Or.inr hi)))
    obtain ⟨D₁, hD₁, S₁, hbound₁⟩ := ih'
    obtain ⟨Ca, hCa, ta, hbounda⟩ := hx a (Finset.mem_cons.mpr (Or.inl rfl))
    refine ⟨Ca + D₁, by linarith, max ta S₁, fun m => ?_⟩
    rw [Finset.sup_cons]
    have h1m : (0 : ℝ) < 1 + (m : ℝ) := by positivity
    have h1m_le : (1 : ℝ) ≤ 1 + (m : ℝ) := by linarith
    have hpow_le_left : (1 + (m : ℝ)) ^ ta ≤ (1 + (m : ℝ)) ^ (max ta S₁) :=
      pow_le_pow_right₀ h1m_le (le_max_left ta S₁)
    have hpow_le_right : (1 + (m : ℝ)) ^ S₁ ≤ (1 + (m : ℝ)) ^ (max ta S₁) :=
      pow_le_pow_right₀ h1m_le (le_max_right ta S₁)
    have hle_sup_left : (p' a) (x m) ≤ (Ca + D₁) * (1 + (m : ℝ)) ^ (max ta S₁) := by
      calc (p' a) (x m) ≤ Ca * (1 + (m : ℝ)) ^ ta := hbounda m
        _ ≤ Ca * (1 + (m : ℝ)) ^ (max ta S₁) :=
            mul_le_mul_of_nonneg_left hpow_le_left (le_of_lt hCa)
        _ ≤ (Ca + D₁) * (1 + (m : ℝ)) ^ (max ta S₁) :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (le_of_lt h1m) _)
    have hle_sup_right : (s.sup p') (x m) ≤ (Ca + D₁) * (1 + (m : ℝ)) ^ (max ta S₁) := by
      calc (s.sup p') (x m) ≤ D₁ * (1 + (m : ℝ)) ^ S₁ := hbound₁ m
        _ ≤ D₁ * (1 + (m : ℝ)) ^ (max ta S₁) :=
            mul_le_mul_of_nonneg_left hpow_le_right (le_of_lt hD₁)
        _ ≤ (Ca + D₁) * (1 + (m : ℝ)) ^ (max ta S₁) :=
            mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (le_of_lt h1m) _)
    exact sup_le hle_sup_left hle_sup_right

/-- **Seminorm bound from Schauder expansion.**

For a continuous seminorm `q` and a Schauder basis with expansion
`f = ∑ₘ cₘ(f) · ψₘ`, the triangle inequality gives
`q(f) ≤ ∑ₘ |cₘ(f)| · q(ψₘ)`.

The proof uses Hahn-Banach to find a CLF `φ` with `φ(f) = q(f)` and `|φ| ≤ q`,
then applies the Schauder expansion to `φ` and bounds the resulting tsum.
-/
lemma seminorm_le_nuclear_expansion
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [hN : DyninMityaginSpace E]
    (q : Seminorm ℝ E) (hq : Continuous q) (f : E) :
    q f ≤ ∑' m, |hN.coeff m f| * q (hN.basis m) := by
  -- Step 1: Hahn-Banach gives φ with φ(f) = q(f) and |φ| ≤ q
  obtain ⟨φ, hφf, hφq⟩ := exists_CLF_le_seminorm q hq f
  -- Step 2: Summability of the target series
  have hsumm : Summable (fun m => |hN.coeff m f| * q (hN.basis m)) := by
    obtain ⟨s₁, C₁, hC₁ne, hqbound⟩ := Seminorm.bound_of_continuous hN.h_with q hq
    have hC₁_pos : (0 : ℝ) < C₁ := by positivity
    have hgrowth : ∀ i ∈ s₁, ∃ C > 0, ∃ t : ℕ,
        ∀ m, hN.p i (hN.basis m) ≤ C * (1 + (m : ℝ)) ^ t :=
      fun i _ => hN.basis_growth i
    classical
    obtain ⟨D, hD, S, hDbound⟩ := finset_sup_poly_bound hN.p s₁ hN.basis hgrowth
    obtain ⟨C₂, hC₂, s₂, hcoeff⟩ := hN.coeff_decay (S + 2)
    have h1m_pos : ∀ m : ℕ, (0 : ℝ) < 1 + (m : ℝ) := fun m => by positivity
    apply Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (apply_nonneg q _))
    · intro m
      calc |hN.coeff m f| * q (hN.basis m)
          ≤ |hN.coeff m f| * ((C₁ : ℝ) * (s₁.sup hN.p) (hN.basis m)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact hqbound (hN.basis m)
        _ ≤ |hN.coeff m f| * ((C₁ : ℝ) * (D * (1 + (m : ℝ)) ^ S)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left (hDbound m) (le_of_lt hC₁_pos)
        _ = (|hN.coeff m f| * (1 + (m : ℝ)) ^ (S + 2)) *
            ((C₁ : ℝ) * D / (1 + (m : ℝ)) ^ 2) := by
            rw [pow_add]; field_simp
        _ ≤ (C₂ * (s₂.sup hN.p) f) * ((C₁ : ℝ) * D / (1 + (m : ℝ)) ^ 2) := by
            apply mul_le_mul_of_nonneg_right (hcoeff f m)
            apply div_nonneg (mul_nonneg (le_of_lt hC₁_pos) (le_of_lt hD))
            positivity
        _ = C₂ * (s₂.sup hN.p) f * (C₁ : ℝ) * D * (1 / ((m : ℝ) + 1) ^ 2) := by
            field_simp; ring
    · have hsumm_shift : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
        have := (summable_nat_add_iff 1).mpr
          (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
        exact this.congr (fun m => by push_cast; ring_nf)
      exact (hsumm_shift.const_smul (C₂ * (s₂.sup hN.p) f * (C₁ : ℝ) * D)).congr
        (fun m => by simp [smul_eq_mul])
  -- Step 3: Summability of the expansion terms
  have hsumm' : Summable (fun m => hN.coeff m f * φ (hN.basis m)) :=
    hsumm.of_norm_bounded (fun m => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hφq _) (abs_nonneg _))
  -- Step 4: Apply expansion axiom and bound the tsum
  rw [← hφf, hN.expansion φ f]
  exact hsumm'.tsum_le_tsum (fun m =>
    le_trans (le_abs_self _)
      (le_trans (le_of_eq (abs_mul _ _))
        (mul_le_mul_of_nonneg_left (hφq _) (abs_nonneg _)))) hsumm

/-! ### Strong Convergence of Schauder Expansion -/

/-- Summability of the Schauder expansion terms in a single seminorm.

For any seminorm index `i` and vector `f`, the series `∑ₘ |cₘ(f)| · pᵢ(ψₘ)` converges.
The proof combines coefficient decay (exponent `S+2`) with basis growth (exponent `S`)
to produce a summable majorant `1/(1+m)²`.
-/
lemma _root_.GaussianField.DyninMityaginSpace.summable_coeff_seminorm_basis
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [hN : DyninMityaginSpace E] (i : hN.ι) (f : E) :
    Summable (fun m => |hN.coeff m f| * hN.p i (hN.basis m)) := by
  obtain ⟨C_g, hC_g, S, hgrowth⟩ := hN.basis_growth i
  obtain ⟨C_d, hC_d, s_d, hdecay⟩ := hN.coeff_decay (S + 2)
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
  · intro m
    calc |hN.coeff m f| * hN.p i (hN.basis m)
        ≤ |hN.coeff m f| * (C_g * (1 + (m : ℝ)) ^ S) :=
          mul_le_mul_of_nonneg_left (hgrowth m) (abs_nonneg _)
      _ = (|hN.coeff m f| * (1 + (m : ℝ)) ^ (S + 2)) *
          (C_g / (1 + (m : ℝ)) ^ 2) := by rw [pow_add]; field_simp
      _ ≤ (C_d * (s_d.sup hN.p) f) * (C_g / (1 + (m : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_right (hdecay f m)
            (div_nonneg (le_of_lt hC_g) (by positivity))
      _ = C_d * (s_d.sup hN.p) f * C_g * (1 / ((m : ℝ) + 1) ^ 2) := by
          field_simp; ring
  · have hsumm_shift : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      exact this.congr (fun m => by push_cast; ring_nf)
    exact (hsumm_shift.const_smul (C_d * (s_d.sup hN.p) f * C_g)).congr
      (fun m => by simp [smul_eq_mul])

/-- **Bound on the Schauder expansion remainder via Hahn-Banach.**

If for every finite set `t` disjoint from `s`, the partial sum
`∑_{m∈t} |c_m(f)| · p_i(ψ_m) ≤ ε`, then the seminorm of the remainder satisfies
`p_i(f - ∑_{m∈s} c_m(f) • ψ_m) ≤ ε`.

The proof uses Hahn-Banach to find a CLF `φ` attaining `p_i` at the error,
then the expansion axiom to express `φ(error)` as a tail of the Schauder series.
-/
private lemma schauder_remainder_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [hN : DyninMityaginSpace E]
    (f : E) (i : hN.ι) (s : Finset ℕ)
    (h_vanish : ∀ t : Finset ℕ, Disjoint t s →
        ∑ m ∈ t, |hN.coeff m f| * hN.p i (hN.basis m) ≤ ε) :
    hN.p i (f - ∑ m ∈ s, hN.coeff m f • hN.basis m) ≤ ε := by
  set err := f - ∑ m ∈ s, hN.coeff m f • hN.basis m
  -- Step 1: Hahn-Banach gives φ with φ(err) = p_i(err) and |φ| ≤ p_i
  obtain ⟨φ, hφerr, hφbound⟩ :=
    exists_CLF_le_seminorm (hN.p i) (hN.h_with.continuous_seminorm i) err
  -- Step 2: The series g m = c_m(f) · φ(ψ_m) is summable (bounded by h)
  set g := fun m => hN.coeff m f * φ (hN.basis m) with hg_def
  set h := fun m => |hN.coeff m f| * hN.p i (hN.basis m) with hh_def
  have hh_sum : Summable h := DyninMityaginSpace.summable_coeff_seminorm_basis i f
  have hg_le_h : ∀ m, ‖g m‖ ≤ h m := fun m => by
    rw [Real.norm_eq_abs, hg_def, abs_mul, hh_def]
    exact mul_le_mul_of_nonneg_left (hφbound _) (abs_nonneg _)
  have hg_summ : Summable g := hh_sum.of_norm_bounded_eventually
    (Filter.Eventually.of_forall hg_le_h)
  -- Step 3: φ(err) = ∑' (m : sᶜ) g m (by expansion axiom + tsum splitting)
  have hφerr_eq : φ err = ∑' (m : ↥(↑s : Set ℕ)ᶜ), g ↑m := by
    have h_lin : φ err = φ f - ∑ m ∈ s, g m := by
      simp [err, map_sub, map_sum, map_smul, smul_eq_mul, g]
    have h_exp := hN.expansion φ f
    rw [h_lin, h_exp, hg_def]
    have h_split := hg_summ.sum_add_tsum_compl (s := s)
    linarith
  -- Step 4: Chain the bounds
  have hg_norm_summ_compl : Summable (fun (m : ↥(↑s : Set ℕ)ᶜ) => ‖g ↑m‖) :=
    (Summable.of_nonneg_of_le (fun m => norm_nonneg _) hg_le_h hh_sum).subtype _
  have hh_summ_compl : Summable (fun (m : ↥(↑s : Set ℕ)ᶜ) => h ↑m) :=
    hh_sum.subtype _
  calc hN.p i err = φ err := hφerr.symm
    _ = |φ err| := by
        rw [abs_of_nonneg]; rw [hφerr]; exact apply_nonneg _ _
    _ = ‖φ err‖ := (Real.norm_eq_abs _).symm
    _ = ‖∑' (m : ↥(↑s : Set ℕ)ᶜ), g ↑m‖ := by rw [hφerr_eq]
    _ ≤ ∑' (m : ↥(↑s : Set ℕ)ᶜ), ‖g ↑m‖ := norm_tsum_le_tsum_norm hg_norm_summ_compl
    _ ≤ ∑' (m : ↥(↑s : Set ℕ)ᶜ), h ↑m :=
        hg_norm_summ_compl.tsum_le_tsum (fun ⟨m, _⟩ => hg_le_h m) hh_summ_compl
    _ ≤ ε := by
        apply hh_summ_compl.tsum_le_of_sum_le
        intro t
        set t' := t.map ⟨Subtype.val, Subtype.val_injective⟩ with ht'_def
        have h_disj : Disjoint t' s := by
          rw [Finset.disjoint_left]
          intro n hn hn_s
          rw [Finset.mem_map] at hn
          obtain ⟨⟨m, hm⟩, _, rfl⟩ := hn
          exact hm hn_s
        have h_le := h_vanish t' h_disj
        rwa [ht'_def, Finset.sum_map] at h_le

/-- **Strong convergence of the Schauder expansion.**

For any `f : E` in a `DyninMityaginSpace`, the series `∑ₘ cₘ(f) • ψₘ` converges to `f`
in the locally convex topology. The proof uses Hahn-Banach for each seminorm
to bound the remainder by the tail of the summable series
`∑ₘ |cₘ(f)| · pᵢ(ψₘ)`.
-/
theorem _root_.GaussianField.DyninMityaginSpace.hasSum_basis
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [hN : DyninMityaginSpace E] (f : E) :
    HasSum (fun m => hN.coeff m f • hN.basis m) f := by
  rw [HasSum]
  change Filter.Tendsto _ Filter.atTop _
  rw [hN.h_with.tendsto_nhds _ f]
  intro i ε hε
  have hh_sum := DyninMityaginSpace.summable_coeff_seminorm_basis i f
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp hh_sum (ε / 2) (half_pos hε)
  rw [Filter.eventually_atTop]
  refine ⟨s₀, fun s hss => ?_⟩
  rw [show (∑ m ∈ s, hN.coeff m f • hN.basis m) - f =
    -(f - ∑ m ∈ s, hN.coeff m f • hN.basis m) from by abel, map_neg_eq_map]
  calc hN.p i (f - ∑ m ∈ s, hN.coeff m f • hN.basis m)
      ≤ ε / 2 := by
        apply schauder_remainder_le f i s
        intro t ht
        have h_disj : Disjoint t s₀ := Disjoint.mono_right hss ht
        have := hs₀ t h_disj
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun m _ =>
          mul_nonneg (abs_nonneg _) (apply_nonneg _ _))] at this
        exact le_of_lt this
    _ < ε := half_lt_self hε

/-! ### Bridge: Dynin-Mityagin → Pietsch -/

/-- **Dynin-Mityagin implies Pietsch nuclearity.**

A `GaussianField.DyninMityaginSpace` (Schauder basis with polynomial growth/decay)
gives rise to a `NuclearSpace` (Pietsch nuclear dominance).

**Proof sketch.** Given a continuous seminorm `p`:

1. Bound `p` by the defining seminorms: `p ≤ C₁ · (s₁.sup hN.p)`
2. Get uniform polynomial growth: `(s₁.sup hN.p)(ψₘ) ≤ D · (1+m)^S`
3. Get coefficient decay with extra room: `|cₘ(f)| · (1+m)^{S+2} ≤ C₂ · (s₂.sup hN.p)(f)`
4. Define CLFs `fₘ := (1+m)^{S+2} · cₘ` and coefficients
   `aₘ := C₁ · D · (1+m)^{-(2:ℤ)}` (summable since exponent < -1)
5. The dominating seminorm is `q := C₁ · s₁.sup(p) + C₂ · s₂.sup(p)`
-/
theorem _root_.GaussianField.DyninMityaginSpace.toNuclearSpace (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [hN : DyninMityaginSpace E] : NuclearSpace E where
  nuclear_dominance := by
    classical
    intro p hp
    -- Step 1: Bound p by the defining seminorms
    obtain ⟨s₁, C₁nn, hC₁ne, hpbound⟩ :=
      Seminorm.bound_of_continuous hN.h_with p hp
    have hC₁_pos : (0 : ℝ) < C₁nn := by positivity
    -- Step 2: Get polynomial growth bound on basis vectors
    have hgrowth : ∀ i ∈ s₁, ∃ C > 0, ∃ t : ℕ,
        ∀ m, hN.p i (hN.basis m) ≤ C * (1 + (m : ℝ)) ^ t :=
      fun i _ => hN.basis_growth i
    obtain ⟨D, hD, S, hDbound⟩ := finset_sup_poly_bound hN.p s₁ hN.basis hgrowth
    -- Step 3: Get coefficient decay with exponent S + 2
    obtain ⟨C₂, hC₂, s₂, hcoeff_decay⟩ := hN.coeff_decay (S + 2)
    -- Build the dominating seminorm q
    set C₂nn : ℝ≥0 := ⟨C₂, le_of_lt hC₂⟩ with hC₂nn_def
    set q := C₁nn • s₁.sup hN.p + C₂nn • s₂.sup hN.p with hq_def
    -- Continuity of finset sups of seminorms
    have hsup_cont : ∀ (t : Finset hN.ι), Continuous (⇑(t.sup hN.p) : E → ℝ) := by
      intro t
      induction t using Finset.cons_induction with
      | empty =>
        change Continuous (⇑(⊥ : Seminorm ℝ E) : E → ℝ)
        simp only [Seminorm.coe_bot]; exact continuous_const
      | cons a t' _ ih =>
        rw [Finset.sup_cons]
        exact (hN.h_with.continuous_seminorm a).sup ih
    have hsup₁_cont : Continuous (⇑(s₁.sup hN.p) : E → ℝ) := hsup_cont s₁
    have hsup₂_cont : Continuous (⇑(s₂.sup hN.p) : E → ℝ) := hsup_cont s₂
    -- q is continuous
    have hq_cont : Continuous q := by
      change Continuous (fun x => q x)
      have : (fun x => q x) = fun x =>
          (C₁nn : ℝ) * (s₁.sup hN.p) x + (C₂nn : ℝ) * (s₂.sup hN.p) x := by
        ext x; simp [hq_def, NNReal.smul_def]
      rw [this]
      exact (continuous_const.mul hsup₁_cont).add (continuous_const.mul hsup₂_cont)
    -- q ≥ p
    have hq_ge : ∀ x, p x ≤ q x := by
      intro x
      have h1 : p x ≤ (C₁nn • s₁.sup hN.p) x := hpbound x
      have h2 : (0 : ℝ) ≤ (C₂nn • s₂.sup hN.p) x := apply_nonneg _ x
      calc p x ≤ (C₁nn • s₁.sup hN.p) x := h1
        _ ≤ (C₁nn • s₁.sup hN.p) x + (C₂nn • s₂.sup hN.p) x := le_add_of_nonneg_right h2
        _ = q x := (Seminorm.add_apply _ _ x).symm
    -- Define CLFs: f_m = (1+m)^{S+2} • coeff m
    let f : ℕ → (E →L[ℝ] ℝ) := fun m => ((1 + (m : ℝ)) ^ (S + 2)) • hN.coeff m
    -- c_m = C₁nn * sup_p(ψ_m) / (1+m)^{S+2}
    let c : ℕ → ℝ := fun m =>
      (C₁nn : ℝ) * (s₁.sup hN.p) (hN.basis m) / (1 + (m : ℝ)) ^ (S + 2)
    -- Common positivity facts
    have h1m_pos : ∀ m : ℕ, (0 : ℝ) < 1 + (m : ℝ) := fun m => by positivity
    have h1m_ne : ∀ m : ℕ, (1 + (m : ℝ)) ≠ 0 := fun m => ne_of_gt (h1m_pos m)
    -- Summability of the shifted p-series ∑ 1/(1+m)^2
    have hsumm_shift : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      exact this.congr (fun m => by push_cast; ring_nf)
    refine ⟨q, hq_cont, hq_ge, f, c, ?_, ?_, ?_, ?_⟩
    -- c ≥ 0
    · intro m
      apply div_nonneg
      · exact mul_nonneg (NNReal.coe_nonneg C₁nn) (apply_nonneg _ _)
      · positivity
    -- Summable c
    · apply Summable.of_nonneg_of_le
      · intro m; exact div_nonneg (mul_nonneg (NNReal.coe_nonneg C₁nn) (apply_nonneg _ _))
          (pow_nonneg (h1m_pos m).le _)
      · intro m
        change (C₁nn : ℝ) * (s₁.sup hN.p) (hN.basis m) / (1 + (m : ℝ)) ^ (S + 2) ≤
          (C₁nn : ℝ) * D / (1 + (m : ℝ)) ^ 2
        have hpow_pos : (0 : ℝ) < (1 + (m : ℝ)) ^ (S + 2) := pow_pos (h1m_pos m) _
        rw [div_le_div_iff₀ hpow_pos (pow_pos (h1m_pos m) 2)]
        calc (C₁nn : ℝ) * (s₁.sup hN.p) (hN.basis m) * (1 + (m : ℝ)) ^ 2
            ≤ (C₁nn : ℝ) * (D * (1 + (m : ℝ)) ^ S) * (1 + (m : ℝ)) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg (h1m_pos m).le 2)
              exact mul_le_mul_of_nonneg_left (hDbound m) (NNReal.coe_nonneg C₁nn)
          _ = (C₁nn : ℝ) * D * ((1 + (m : ℝ)) ^ S * (1 + (m : ℝ)) ^ 2) := by ring
          _ = (C₁nn : ℝ) * D * (1 + (m : ℝ)) ^ (S + 2) := by rw [pow_add]
      · have : Summable (fun m : ℕ => (C₁nn : ℝ) * D * ((1 : ℝ) / ((m : ℝ) + 1) ^ 2)) :=
          hsumm_shift.const_smul ((C₁nn : ℝ) * D)
        exact this.congr (fun m => by ring_nf)
    -- ‖f m x‖ ≤ q x
    · intro m x
      change ‖((1 + (m : ℝ)) ^ (S + 2)) • hN.coeff m x‖ ≤ q x
      simp only [smul_eq_mul, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (pow_nonneg (h1m_pos m).le _)]
      rw [mul_comm]
      calc |hN.coeff m x| * (1 + (m : ℝ)) ^ (S + 2) ≤ C₂ * (s₂.sup hN.p) x :=
              hcoeff_decay x m
        _ = (C₂nn : ℝ) * (s₂.sup hN.p) x := rfl
        _ = (C₂nn • s₂.sup hN.p) x := by simp [NNReal.smul_def]
        _ ≤ (C₁nn • s₁.sup hN.p) x + (C₂nn • s₂.sup hN.p) x :=
            le_add_of_nonneg_left (apply_nonneg _ x)
        _ = q x := (Seminorm.add_apply _ _ x).symm
    -- p x ≤ ∑' m, ‖f m x‖ * c m
    · intro x
      have hexpand := seminorm_le_nuclear_expansion (s₁.sup hN.p) hsup₁_cont x
      have hsum_eq : (C₁nn : ℝ) * ∑' m, |hN.coeff m x| * (s₁.sup hN.p) (hN.basis m) =
          ∑' m, ‖f m x‖ * c m := by
        rw [← tsum_mul_left]
        congr 1; ext m
        change (C₁nn : ℝ) * (|hN.coeff m x| * (s₁.sup hN.p) (hN.basis m)) =
          ‖((1 + (m : ℝ)) ^ (S + 2)) • hN.coeff m x‖ *
          ((C₁nn : ℝ) * (s₁.sup hN.p) (hN.basis m) / (1 + (m : ℝ)) ^ (S + 2))
        simp only [smul_eq_mul, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (pow_nonneg (h1m_pos m).le _)]
        field_simp
      calc p x ≤ (C₁nn • s₁.sup hN.p) x := hpbound x
        _ = (C₁nn : ℝ) * (s₁.sup hN.p) x := by simp [NNReal.smul_def]
        _ ≤ (C₁nn : ℝ) * ∑' m, |hN.coeff m x| * (s₁.sup hN.p) (hN.basis m) :=
            mul_le_mul_of_nonneg_left hexpand (NNReal.coe_nonneg C₁nn)
        _ = ∑' m, ‖f m x‖ * c m := hsum_eq

end GaussianField
