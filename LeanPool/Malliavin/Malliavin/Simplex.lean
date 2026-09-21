/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.Symmetrization

/-!
# Rung 2 prerequisite: the simplex `Δₙ` and the tiling `Tⁿ = ⨆_σ σ·Δₙ` (mod null sets)

Iterated Itô integrals `Jₙ(g) = ∫_{t₁<⋯<tₙ} g dW_{t₁}⋯dW_{tₙ}` live on the simplex
`Δₙ = {t : Fin n → T | StrictMono t}`, whereas the multiple Wiener–Itô integral `Iₙ(f)` uses all of
`Tⁿ`. The bridge is purely deterministic: `Tⁿ` is the disjoint union of the `n!` permuted copies
`sortedBy σ = {t | StrictMono (t ∘ σ)}` of the simplex, up to the `μ^{⊗n}`-null "diagonal"
`{t | ¬ Injective t}` (null as soon as `μ` has no atoms, i.e. `NullSingletonClass μ`). Hence,
for symmetric `g`,

  `∫ g dμ^{⊗n} = n! • ∫_{Δₙ} g dμ^{⊗n}`,

which is what turns `E[Jₙ(f_sym)²] = ‖f_sym‖²_{L²(Δₙ)}` into `E[Iₙ(f)²] = n! ‖f_sym‖²_{L²(Tⁿ)}`
(Nualart, *The Malliavin Calculus and Related Topics*, §1.1.2).

## Main results

* `Malliavin.simplex`, `Malliavin.sortedBy`, `Malliavin.diagonal` — the sets involved.
* `Malliavin.exists_strictMono_comp_of_injective`, `Malliavin.perm_eq_of_strictMono_comp` —
  an injective tuple is sorted by exactly one permutation (via `Tuple.sort`).
* `Malliavin.disjoint_sortedBy`, `Malliavin.iUnion_sortedBy_eq` — the tiling.
* `Malliavin.measurableSet_simplex`, `Malliavin.measurableSet_sortedBy`,
  `Malliavin.measurableSet_diagonal`.
* `Malliavin.setIntegral_sortedBy` — every tile carries the same integral of a symmetric function.
* `Malliavin.measure_diagonal_eq_zero` — the diagonal is `μ^{⊗n}`-null for `NullSingletonClass μ`.
* `Malliavin.integral_eq_factorial_smul_setIntegral_simplex` — `∫ g = n! • ∫_{Δₙ} g` for
  symmetric `g`;
* `Malliavin.integral_eq_factorial_smul_setIntegral_symmetrize` — `∫ g = n! • ∫_{Δₙ} g_sym` for any
  integrable `g`;
  `Malliavin.integral_sq_norm_eq_factorial_smul` — its `L²` form `∫ ‖g‖² = n! • ∫_{Δₙ} ‖g‖²`.
-/

open MeasureTheory Finset Set
open scoped ENNReal

noncomputable
section

namespace Malliavin

variable {T : Type*} {E : Type*}

/-- Post-composition preserves symmetry. -/
theorem IsSymmetric.comp_left {n : ℕ} {g : (Fin n → T) → E} (hg : IsSymmetric n g)
    {F : Type*} (φ : E → F) : IsSymmetric n (φ ∘ g) :=
  fun σ t => by simp only [Function.comp_apply, hg σ t]

/-- The "diagonal": tuples with a repeated coordinate. -/
def diagonal (T : Type*) (n : ℕ) : Set (Fin n → T) :=
  {t | ¬ Function.Injective t}

theorem mem_diagonal {n : ℕ} {t : Fin n → T} : t ∈ diagonal T n ↔ ¬ Function.Injective t :=
  Iff.rfl

theorem diagonal_eq_iUnion (n : ℕ) :
    diagonal T n = ⋃ (i : Fin n) (j : Fin n) (_ : i ≠ j), {t : Fin n → T | t i = t j} := by
  ext t
  constructor
  · intro ht
    simp only [mem_diagonal, Function.Injective] at ht
    push Not at ht
    obtain ⟨i, j, hij, hne⟩ := ht
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hne, hij⟩⟩⟩
  · intro ht hinj
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ht
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hi
    obtain ⟨hne, hij⟩ := Set.mem_iUnion.1 hj
    exact hne (hinj hij)

/-! ### The combinatorial tiling -/

section Order

variable [LinearOrder T]

/-- The (open) simplex `Δₙ = {t : Fin n → T | t 0 < t 1 < ⋯ < t (n-1)}`. -/
def simplex (T : Type*) [LinearOrder T] (n : ℕ) : Set (Fin n → T) :=
  {t | StrictMono t}

theorem mem_simplex {n : ℕ} {t : Fin n → T} : t ∈ simplex T n ↔ StrictMono t :=
  Iff.rfl

/-- The tuples sorted by `σ`: the preimage of the simplex under `t ↦ t ∘ σ`. -/
def sortedBy (T : Type*) [LinearOrder T] (n : ℕ) (σ : Equiv.Perm (Fin n)) : Set (Fin n → T) :=
  (fun t : Fin n → T => t ∘ σ) ⁻¹' simplex T n

theorem mem_sortedBy {n : ℕ} {σ : Equiv.Perm (Fin n)} {t : Fin n → T} :
    t ∈ sortedBy T n σ ↔ StrictMono (t ∘ σ) :=
  Iff.rfl

theorem sortedBy_one (n : ℕ) : sortedBy T n 1 = simplex T n := by
  ext t
  simp only [mem_sortedBy, Equiv.Perm.coe_one, CompTriple.comp_eq, mem_simplex]

theorem injective_of_strictMono_comp {n : ℕ} {t : Fin n → T} {σ : Equiv.Perm (Fin n)}
    (h : StrictMono (t ∘ σ)) : Function.Injective t := by
  have e : t = (t ∘ σ) ∘ σ.symm := by
    ext i
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [e]
  exact h.injective.comp σ.symm.injective

/-- Every injective tuple is sorted by some permutation (namely `Tuple.sort`). -/
theorem exists_strictMono_comp_of_injective {n : ℕ} {t : Fin n → T}
    (ht : Function.Injective t) : ∃ σ : Equiv.Perm (Fin n), StrictMono (t ∘ σ) :=
  ⟨Tuple.sort t,
    (Tuple.monotone_sort t).strictMono_of_injective (ht.comp (Tuple.sort t).injective)⟩

/-- The sorting permutation of an injective tuple is unique. -/
theorem perm_eq_of_strictMono_comp {n : ℕ} {t : Fin n → T} (ht : Function.Injective t)
    {σ τ : Equiv.Perm (Fin n)} (hσ : StrictMono (t ∘ σ)) (hτ : StrictMono (t ∘ τ)) : σ = τ := by
  have hrange : Set.range (t ∘ σ) = Set.range (t ∘ τ) := by
    rw [σ.surjective.range_comp, τ.surjective.range_comp]
  have h : t ∘ σ = t ∘ τ := (hσ.range_inj_of_wellFoundedLT hτ).1 hrange
  exact Equiv.coe_fn_injective (ht.comp_left h)

theorem disjoint_sortedBy {n : ℕ} {σ τ : Equiv.Perm (Fin n)} (h : σ ≠ τ) :
    Disjoint (sortedBy T n σ) (sortedBy T n τ) := by
  rw [Set.disjoint_left]
  intro t hσ hτ
  exact h (perm_eq_of_strictMono_comp (injective_of_strictMono_comp hσ) hσ hτ)

/-- The tiles `sortedBy σ` cover exactly the injective tuples. -/
theorem iUnion_sortedBy_eq (n : ℕ) :
    ⋃ σ : Equiv.Perm (Fin n), sortedBy T n σ = (diagonal T n)ᶜ := by
  ext t
  constructor
  · intro ht
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 ht
    exact fun h => h (injective_of_strictMono_comp hσ)
  · intro ht
    obtain ⟨σ, hσ⟩ := exists_strictMono_comp_of_injective (not_not.1 ht)
    exact Set.mem_iUnion.2 ⟨σ, hσ⟩

end Order

/-! ### Measurability -/

section MeasurableComp

variable [MeasurableSpace T]

theorem measurable_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Measurable fun t : Fin n → T => t ∘ σ :=
  Measurable.of_eval fun i => measurable_pi_apply (σ i)

end MeasurableComp

section Measurable

variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]

theorem measurableSet_simplex (n : ℕ) : MeasurableSet (simplex T n) := by
  have : simplex T n =
      ⋂ (i : Fin n) (j : Fin n) (_ : i < j), {t : Fin n → T | t i < t j} := by
    ext t
    simp only [mem_simplex, Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

theorem measurableSet_sortedBy (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurableSet (sortedBy T n σ) :=
  (measurableSet_simplex n).preimage (measurable_comp_perm n σ)

theorem measurableSet_diagonal (n : ℕ) : MeasurableSet (diagonal T n) := by
  rw [diagonal_eq_iUnion]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    MeasurableSet.iUnion fun _ => ?_
  have : {t : Fin n → T | t i = t j} = {t | t i ≤ t j} ∩ {t | t j ≤ t i} := by
    ext t
    simp only [le_antisymm_iff, mem_ofPred_eq, mem_inter_iff]
  rw [this]
  exact (measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)).inter
    (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i))

end Measurable

/-! ### The integral identity `∫ g = n! • ∫_{Δₙ} g` for symmetric `g` -/

section Integral

variable [MeasurableSpace T] [TopologicalSpace T] [LinearOrder T] [OrderClosedTopology T]
  [SecondCountableTopology T] [OpensMeasurableSpace T]
variable {μ : Measure T} [SigmaFinite μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `i ≠ j`, the "hyperplane" `{t | t i = t j}` is `μ^{⊗n}`-null when `μ` has no atoms:
split off the coordinate `i` with `piFinSuccAbove` and apply Fubini (`Measure.prod_apply`). -/
theorem measure_coord_eq_zero [NullSingletonClass μ] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Measure.pi (fun _ : Fin n => μ) {t : Fin n → T | t i = t j} = 0 := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    subst hk
    let e : (Fin (m + 1) → T) ≃ᵐ T × (Fin m → T) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => T) i
    have hmp : MeasurePreserving e (Measure.pi fun _ : Fin (m + 1) => μ)
        (μ.prod (Measure.pi fun _ : Fin m => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) i
    let s : Set (T × (Fin m → T)) := {p | p.1 = p.2 k}
    have hs : MeasurableSet s := by
      have : s = {p : T × (Fin m → T) | p.1 ≤ p.2 k} ∩ {p | p.2 k ≤ p.1} := by
        ext p
        simp only [le_antisymm_iff, mem_ofPred_eq, mem_inter_iff, s]
      rw [this]
      exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
        (measurableSet_le (by fun_prop) (by fun_prop))
    have hpre : {t : Fin (m + 1) → T | t i = t (i.succAbove k)} = e ⁻¹' s := rfl
    have h0 : ∀ x : T, (Measure.pi fun _ : Fin m => μ) (Prod.mk x ⁻¹' s) = 0 := by
      intro x
      have hset : Prod.mk x ⁻¹' s =
          Set.pi Set.univ (Function.update (fun _ : Fin m => (Set.univ : Set T)) k {x}) := by
        ext u
        simp only [s, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ_pi]
        constructor
        · intro h l
          by_cases hl : l = k
          · rw [hl]
            simp only [h, Function.update_self, mem_singleton_iff]
          · simp only [ne_eq, hl, not_false_eq_true, Function.update_of_ne, Set.mem_univ]
        · intro h
          have hk := h k
          simp only [Function.update_self, mem_singleton_iff] at hk
          exact hk.symm
      rw [hset, Measure.pi_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ k)
        (by simp [(Set.subsingleton_singleton).measure_zero μ])
    rw [hpre, ← Measure.map_apply hmp.measurable hs, hmp.map_eq, Measure.prod_apply hs]
    simp only [h0, lintegral_const, zero_mul]

/-- The diagonal is `μ^{⊗n}`-null when `μ` has no atoms. -/
theorem measure_diagonal_eq_zero [NullSingletonClass μ] (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) (diagonal T n) = 0 := by
  rw [diagonal_eq_iUnion]
  exact measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij =>
    measure_coord_eq_zero hij

theorem ae_injective [NullSingletonClass μ] (n : ℕ) :
    ∀ᵐ t ∂(Measure.pi fun _ : Fin n => μ), Function.Injective t :=
  ae_iff.2 (measure_diagonal_eq_zero n)

/-- Almost every tuple is sorted by exactly one permutation. -/
theorem ae_existsUnique_mem_sortedBy [NullSingletonClass μ] (n : ℕ) :
    ∀ᵐ t ∂(Measure.pi fun _ : Fin n => μ), ∃! σ : Equiv.Perm (Fin n), t ∈ sortedBy T n σ := by
  filter_upwards [ae_injective (μ := μ) n] with t ht
  obtain ⟨σ, hσ⟩ := exists_strictMono_comp_of_injective ht
  exact ⟨σ, hσ, fun τ hτ => perm_eq_of_strictMono_comp ht hτ hσ⟩

/-- Every tile `sortedBy σ` carries the same integral of a symmetric function as the simplex. -/
theorem setIntegral_sortedBy {n : ℕ} {g : (Fin n → T) → E} (hg : IsSymmetric n g)
    (σ : Equiv.Perm (Fin n)) :
    ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) =
      ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) := by
  have hemb : MeasurableEmbedding (fun t : Fin n → T => t ∘ σ) :=
    (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl T)).measurableEmbedding
  calc ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ t in (fun t : Fin n → T => t ∘ σ) ⁻¹' simplex T n, g (t ∘ σ)
          ∂(Measure.pi fun _ : Fin n => μ) :=
        setIntegral_congr_fun (measurableSet_sortedBy n σ) fun t _ => (hg σ t).symm
    _ = ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        (measurePreserving_comp_perm μ n σ).setIntegral_preimage_emb hemb g _

/-- **Tiling identity**: for symmetric integrable `g`, `∫ g dμ^{⊗n} = n! • ∫_{Δₙ} g dμ^{⊗n}`. -/
theorem integral_eq_factorial_smul_setIntegral_simplex [NullSingletonClass μ] {n : ℕ}
    {g : (Fin n → T) → E} (hg : IsSymmetric n g)
    (hint : Integrable g (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, g t ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) := by
  have hdiag : ((diagonal T n)ᶜ : Set (Fin n → T)) =ᵐ[Measure.pi fun _ : Fin n => μ]
      (Set.univ : Set (Fin n → T)) := by
    rw [ae_eq_univ, compl_compl]
    exact measure_diagonal_eq_zero n
  calc ∫ t, g t ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ t in (diagonal T n)ᶜ, g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [setIntegral_congr_set hdiag, Measure.restrict_univ]
    _ = ∫ t in ⋃ σ : Equiv.Perm (Fin n), sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [iUnion_sortedBy_eq]
    _ = ∑' σ : Equiv.Perm (Fin n), ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        integral_iUnion (measurableSet_sortedBy n) (fun _ _ hστ => disjoint_sortedBy hστ)
          hint.integrableOn
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        tsum_fintype _
    _ = ∑ _σ : Equiv.Perm (Fin n), ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        Finset.sum_congr rfl fun σ _ => setIntegral_sortedBy hg σ
    _ = n.factorial • ∫ t in simplex T n, g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- **Tiling identity, general form**: for any integrable `g`,
`∫ g dμ^{⊗n} = n! • ∫_{Δₙ} (symmetrize n g) dμ^{⊗n}` — the deterministic shadow of
`Iₙ(f) = Iₙ(f_sym)`. -/
theorem integral_eq_factorial_smul_setIntegral_symmetrize [NullSingletonClass μ] {n : ℕ}
    {g : (Fin n → T) → E} (hint : Integrable g (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, g t ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, symmetrize n g t ∂(Measure.pi fun _ : Fin n => μ) := by
  have hdiag : ((diagonal T n)ᶜ : Set (Fin n → T)) =ᵐ[Measure.pi fun _ : Fin n => μ]
      (Set.univ : Set (Fin n → T)) := by
    rw [ae_eq_univ, compl_compl]
    exact measure_diagonal_eq_zero n
  -- each tile: `∫_{sortedBy σ} g = ∫_{Δₙ} g (u ∘ ⇑(σ⁻¹))`
  have htile : ∀ σ : Equiv.Perm (Fin n),
      ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) =
        ∫ u in simplex T n, g (u ∘ ⇑(σ⁻¹)) ∂(Measure.pi fun _ : Fin n => μ) := by
    intro σ
    have hemb : MeasurableEmbedding (fun t : Fin n → T => t ∘ σ) :=
      (MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl T)).measurableEmbedding
    refine Eq.trans ?_ ((measurePreserving_comp_perm μ n σ).setIntegral_preimage_emb hemb
      (fun u => g (u ∘ ⇑(σ⁻¹))) (simplex T n))
    refine setIntegral_congr_fun (measurableSet_sortedBy n σ) fun t _ => ?_
    congr 1
    ext i
    simp only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
  calc ∫ t, g t ∂(Measure.pi fun _ : Fin n => μ)
      = ∫ t in (diagonal T n)ᶜ, g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [setIntegral_congr_set hdiag, Measure.restrict_univ]
    _ = ∫ t in ⋃ σ : Equiv.Perm (Fin n), sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [iUnion_sortedBy_eq]
    _ = ∑' σ : Equiv.Perm (Fin n), ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        integral_iUnion (measurableSet_sortedBy n) (fun _ _ hστ => disjoint_sortedBy hστ)
          hint.integrableOn
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ t in sortedBy T n σ, g t ∂(Measure.pi fun _ : Fin n => μ) :=
        tsum_fintype _
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ u in simplex T n, g (u ∘ ⇑(σ⁻¹))
          ∂(Measure.pi fun _ : Fin n => μ) :=
        Finset.sum_congr rfl fun σ _ => htile σ
    _ = ∑ σ : Equiv.Perm (Fin n), ∫ u in simplex T n, g (u ∘ σ) ∂(Measure.pi fun _ : Fin n => μ) :=
        Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))
          (fun σ => ∫ u in simplex T n, g (u ∘ σ) ∂(Measure.pi fun _ : Fin n => μ))
    _ = ∫ u in simplex T n, ∑ σ : Equiv.Perm (Fin n), g (u ∘ σ) ∂(Measure.pi fun _ : Fin n => μ) :=
        (integral_finsetSum _ fun σ _ =>
          (memLp_one_iff_integrable.1 ((memLp_one_iff_integrable.2 hint).comp_measurePreserving
            (measurePreserving_comp_perm μ n σ))).integrableOn).symm
    _ = n.factorial • ∫ t in simplex T n, symmetrize n g t ∂(Measure.pi fun _ : Fin n => μ) := by
        rw [← Nat.cast_smul_eq_nsmul ℝ]
        simp_rw [symmetrize_apply]
        rw [integral_smul, smul_smul, mul_inv_cancel₀ (by exact_mod_cast n.factorial_ne_zero),
          one_smul]

omit [NormedSpace ℝ E] in
/-- The `L²` form of the tiling identity: `∫ ‖g‖² = n! • ∫_{Δₙ} ‖g‖²` for symmetric `g ∈ L²`.
This is the identity that turns `E[Jₙ(g)²] = ‖g‖²_{L²(Δₙ)}` into `E[Iₙ(g)²] = n! ‖g‖²_{L²(Tⁿ)}`. -/
theorem integral_sq_norm_eq_factorial_smul [NullSingletonClass μ] {n : ℕ} {g : (Fin n → T) → E}
    (hg : IsSymmetric n g) (hg2 : MemLp g 2 (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, ‖g t‖ ^ 2 ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, ‖g t‖ ^ 2 ∂(Measure.pi fun _ : Fin n => μ) :=
  integral_eq_factorial_smul_setIntegral_simplex (E := ℝ) (hg.comp_left fun x => ‖x‖ ^ 2)
    ((memLp_two_iff_integrable_sq_norm hg2.aestronglyMeasurable).1 hg2)

/-- Specialisation to a symmetrized function: `∫ f_sym = n! • ∫_{Δₙ} f_sym`. -/
theorem integral_symmetrize_eq_factorial_smul [NullSingletonClass μ] {n : ℕ} {f : (Fin n → T) → E}
    (hint : Integrable (symmetrize n f) (Measure.pi fun _ : Fin n => μ)) :
    ∫ t, symmetrize n f t ∂(Measure.pi fun _ : Fin n => μ) =
      n.factorial • ∫ t in simplex T n, symmetrize n f t ∂(Measure.pi fun _ : Fin n => μ) :=
  integral_eq_factorial_smul_setIntegral_simplex (isSymmetric_symmetrize n f) hint

end Integral

end Malliavin

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
