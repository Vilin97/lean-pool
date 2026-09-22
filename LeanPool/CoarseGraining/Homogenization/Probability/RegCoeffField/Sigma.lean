/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The carrier σ-algebra, its additive structure, and the layered builder

This file equips the carrier `RegCoeffField d` (see `RegCoeffField.lean`) with a
measurable structure and proves the facts that make it usable as a probability
carrier for the homogenization development.

* `IsProbeR` — the enriched probe class (bounded, measurable, compactly
  supported scalar test functions), adapted from the raw-`CoeffField`
  `IsProbe` of the salvage branch; the closure lemmas `of_smooth`, `indicator`,
  `comp_homeomorph` are carried over.
* `entryTestR i j φ a = ∫ a(x)_{ij} · φ(x) dx` — the linear single-entry
  generator, which is **genuinely additive** on the carrier
  (`entryTestR_add`): the integrand `a(·)_{ij} · φ` is honestly integrable
  because `a(·)_{ij}` is locally integrable and `φ` is a probe.
* `pointwiseSigmaR`, `entryTestSigmaR`, and the canonical instance
  `instMeasurableSpaceRegCoeffField = pointwiseSigmaR ⊔ entryTestSigmaR`.
* the builder criterion `measurable_into_regCoeffField'`, and the crux
  `instMeasurableAdd₂`: **addition is genuinely measurable at the join**.
* `measurable_layeredBuilder`: base plus a finite sum of measurable layer maps
  is a genuinely measurable carrier-valued map — the acceptance theorem.
* endomorphism transport (`adjointReg`, `measurable_adjointReg`, and the general
  `measurable_of_entryTestR_transport`), and `RegCoeffLaw d = Measure ...`.

The raw `CoeffField`'s ambient σ-algebra is deliberately kept out of scope here,
so the pi structure on `Vec d → Mat d` is the one used throughout (the paper,
Armstrong–Kuusi–Loher, to appear).
-/

namespace Homogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The entrywise (pi) measurable space on `Mat d`.  Declared here — rather than
importing the raw-`CoeffField` layer — so that the raw ambient σ-algebra on
`Vec d → Mat d` stays out of scope and coordinate evaluation is governed by the
pi structure. -/
instance instMatMeasurableSpace (d : ℕ) : MeasurableSpace (Mat d) := by
  change MeasurableSpace (Fin d → Fin d → ℝ); infer_instance

/-! ## Probes -/

/-- The enriched probe class: bounded, measurable, compactly supported scalar
test functions on `Vec d`.  Bounded measurability (rather than continuity) is
what keeps the class closed under multiplication by indicators, and is exactly
enough to make the entry generator additive on the carrier (the paper,
Armstrong–Kuusi–Loher, to appear). -/
structure IsProbeR (φ : Vec d → ℝ) : Prop where
  /-- The probe is Borel measurable. -/
  measurable : Measurable φ
  /-- The probe is uniformly bounded. -/
  bounded : ∃ C : ℝ, ∀ x, |φ x| ≤ C
  /-- The probe has compact support. -/
  hasCompactSupport : HasCompactSupport φ

/-- The support of `Set.indicator U φ` is contained in the support of `φ`. -/
private theorem support_indicator_subset_support (U : Set (Vec d)) (φ : Vec d → ℝ) :
    Function.support (Set.indicator U φ) ⊆ Function.support φ := by
  classical
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h; apply hx; rw [Set.indicator_apply]; simp [h]

/-- Smooth compactly-supported probes are enriched probes. -/
theorem IsProbeR.of_smooth {φ : Vec d → ℝ} (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcs : HasCompactSupport φ) : IsProbeR φ := by
  refine ⟨hcont.continuous.measurable, ?_, hcs⟩
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont.continuous
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩

/-- The enriched probe class is closed under multiplication by the indicator of a
measurable set. -/
theorem IsProbeR.indicator {φ : Vec d → ℝ} (hφ : IsProbeR φ) {U : Set (Vec d)}
    (hU : MeasurableSet U) : IsProbeR (Set.indicator U φ) := by
  refine ⟨hφ.measurable.indicator hU, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hφ.bounded
    refine ⟨C, fun x => ?_⟩
    by_cases hx : x ∈ U
    · simpa [Set.indicator_of_mem hx] using hC x
    · simp only [Set.indicator_of_notMem hx, abs_zero]
      exact le_trans (abs_nonneg _) (hC x)
  · exact HasCompactSupport.mono hφ.hasCompactSupport (support_indicator_subset_support U φ)

/-- The enriched probe class is closed under precomposition with a homeomorphism
of the base space (translation/signed-permutation/rescaling transport). -/
theorem IsProbeR.comp_homeomorph {φ : Vec d → ℝ} (hφ : IsProbeR φ)
    (h : Vec d ≃ₜ Vec d) : IsProbeR (φ ∘ h) := by
  obtain ⟨C, hC⟩ := hφ.bounded
  exact ⟨hφ.measurable.comp h.continuous.measurable, ⟨C, fun x => hC (h x)⟩,
    hφ.hasCompactSupport.comp_homeomorph h⟩

/-! ## The linear entry generator and its additivity -/

/-- The linear single-entry generator on the carrier: `∫ a(x)_{ij} · φ(x) dx`. -/
def entryTestR (i j : Fin d) (φ : Vec d → ℝ) (a : RegCoeffField d) : ℝ :=
  ∫ x, a x i j * φ x ∂volume

/-- On the carrier, the integrand `a(·)_{ij} · φ` of a probe is genuinely
integrable: `a(·)_{ij}` is locally integrable and `φ` is bounded, measurable and
compactly supported, so the product is integrable on the (compact) support of
`φ` and vanishes off it. -/
theorem integrable_entry_mul_probe (i j : Fin d) {φ : Vec d → ℝ} (hφ : IsProbeR φ)
    (a : RegCoeffField d) : Integrable (fun x => a x i j * φ x) volume := by
  set K := tsupport φ with hKdef
  have hK : IsCompact K := hφ.hasCompactSupport
  obtain ⟨C, hC⟩ := hφ.bounded
  have hIntOn : IntegrableOn (fun x => a x i j) K volume :=
    (a.entry_locInt i j).integrableOn_isCompact hK
  have hmulOn : IntegrableOn (fun x => a x i j * φ x) K volume := by
    refine hIntOn.mul_bdd (c := C) hφ.measurable.aestronglyMeasurable.restrict ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hC x
  have hself : K.indicator (fun x => a x i j * φ x) = fun x => a x i j * φ x := by
    apply Set.indicator_eq_self.2
    apply Function.support_subset_iff'.2
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← hself, integrable_indicator_iff hK.measurableSet]
  exact hmulOn

/-- **Genuine additivity of the entry generator on the carrier.** -/
theorem entryTestR_add (i j : Fin d) {φ : Vec d → ℝ} (hφ : IsProbeR φ)
    (a b : RegCoeffField d) :
    entryTestR i j φ (a + b) = entryTestR i j φ a + entryTestR i j φ b := by
  unfold entryTestR
  rw [← integral_add (integrable_entry_mul_probe i j hφ a)
    (integrable_entry_mul_probe i j hφ b)]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp only [RegCoeffField.add_apply, Matrix.add_apply]
  ring

@[simp] theorem entryTestR_zero (i j : Fin d) (φ : Vec d → ℝ) :
    entryTestR i j φ (0 : RegCoeffField d) = 0 := by
  unfold entryTestR; simp

theorem entryTestR_smul (i j : Fin d) {φ : Vec d → ℝ} (c : ℝ) (a : RegCoeffField d) :
    entryTestR i j φ (c • a) = c * entryTestR i j φ a := by
  unfold entryTestR
  simp only [RegCoeffField.smul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with x
  ring

/-- `entryTestR` distributes over finite sums on the carrier. -/
theorem entryTestR_finsetSum {ι : Type*} (i j : Fin d) {φ : Vec d → ℝ}
    (hφ : IsProbeR φ) (s : Finset ι) (g : ι → RegCoeffField d) :
    entryTestR i j φ (∑ l ∈ s, g l) = ∑ l ∈ s, entryTestR i j φ (g l) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert l s hl ih =>
      rw [Finset.sum_insert hl, Finset.sum_insert hl, entryTestR_add i j hφ, ih]

/-! ## The carrier σ-algebra -/
/-- The pointwise (product) σ-algebra: the comap of the underlying map into the
pi σ-algebra on `Vec d → Mat d`. -/
def pointwiseSigmaR (d : ℕ) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.comap RegCoeffField.toFun MeasurableSpace.pi
/-- The entry-test σ-algebra: generated by the preimages of the linear entry
generators over the enriched probe class. -/
def entryTestSigmaR (d : ℕ) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTestR i j φ ⁻¹' t}

/-- The canonical measurable structure on the carrier: the join of the pointwise
and entry-test σ-algebras.  Both generating families are additive, so this join
supports a genuine `MeasurableAdd₂` (see `instMeasurableAdd₂`). -/
instance instMeasurableSpaceRegCoeffField (d : ℕ) : MeasurableSpace (RegCoeffField d) :=
  pointwiseSigmaR d ⊔ entryTestSigmaR d

theorem pointwiseSigmaR_le (d : ℕ) :
    pointwiseSigmaR d ≤ instMeasurableSpaceRegCoeffField d := le_sup_left

theorem entryTestSigmaR_le (d : ℕ) :
    entryTestSigmaR d ≤ instMeasurableSpaceRegCoeffField d := le_sup_right
/-- The **local** carrier σ-algebra on an observation set `U`: generated by the
entry-test preimages using only probes supported in `U`.  This is the honest
carrier analog of the raw-`CoeffField` `PointwiseLocalSigma U`: it records exactly the
information about a field carried by linear entry tests localized to `U`.  Unlike
the raw fine `PointwiseLocalSigma`, it is coarser than the canonical carrier σ-algebra
(`LocalSigmaR_le`), so bounded local events are genuinely measurable — the
carrier win over the powerset-fine raw local σ-algebra (the paper,
Armstrong–Kuusi–Loher, to appear). -/
def LocalSigmaR (U : Set (Vec d)) : MeasurableSpace (RegCoeffField d) :=
  MeasurableSpace.generateFrom
    {s | ∃ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ ∧ Function.support φ ⊆ U ∧
      ∃ t : Set ℝ, MeasurableSet t ∧ s = entryTestR i j φ ⁻¹' t}

/-! ## Measurability infrastructure -/

/-- Measurability into a join reduces to measurability into each summand. -/
theorem measurable_into_sup {α β : Type*} {dom : MeasurableSpace α}
    {m1 m2 : MeasurableSpace β} {f : α → β}
    (h1 : @Measurable α β dom m1 f) (h2 : @Measurable α β dom m2 f) :
    @Measurable α β dom (m1 ⊔ m2) f := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_sup]
  exact sup_le h1.comap_le h2.comap_le

/-- A map into `Mat d` is measurable iff every scalar entry is measurable. -/
theorem measurable_matrix_of_entries {α : Type*} [MeasurableSpace α] {h : α → Mat d}
    (H : ∀ i j, Measurable (fun a => h a i j)) : Measurable h :=
  measurable_pi_lambda (fun i => measurable_pi_lambda (fun j => H i j))

/-- A carrier-valued map is pointwise (pi-)measurable iff every scalar entry
evaluation is measurable. -/
theorem measurable_toFun_of_entries {α : Type*} [MeasurableSpace α]
    {F : α → RegCoeffField d} (H : ∀ (y : Vec d) (i j : Fin d), Measurable (fun a => F a y i j)) :
    @Measurable α (Vec d → Mat d) _ MeasurableSpace.pi (fun a => (F a).toFun) :=
  measurable_pi_lambda (fun y => measurable_matrix_of_entries (fun i j => H y i j))

/-- Builder for the pointwise lane. -/
theorem measurable_into_pointwiseSigmaR {α : Type*} [MeasurableSpace α]
    {F : α → RegCoeffField d}
    (h : @Measurable α (Vec d → Mat d) _ MeasurableSpace.pi (fun a => (F a).toFun)) :
    @Measurable α (RegCoeffField d) _ (pointwiseSigmaR d) F := by
  rw [measurable_iff_comap_le, pointwiseSigmaR, MeasurableSpace.comap_comp]
  exact h.comap_le

/-- Builder for the entry-test lane: measurable into `entryTestSigmaR` iff every
generator functional is measurable after the map. -/
theorem measurable_into_entryTestSigmaR {α : Type*} [MeasurableSpace α]
    {F : α → RegCoeffField d}
    (h : ∀ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ →
      Measurable (fun a => entryTestR i j φ (F a))) :
    @Measurable α (RegCoeffField d) _ (entryTestSigmaR d) F := by
  refine measurable_generateFrom ?_
  rintro s ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact h i j φ hφ ht

/-- **Builder criterion at the join.**  A map into the carrier is measurable for
the canonical σ-algebra iff every scalar entry evaluation is measurable
(pointwise lane) and every entry generator functional is measurable (entry-test
lane). -/
theorem measurable_into_regCoeffField' {α : Type*} [MeasurableSpace α]
    {F : α → RegCoeffField d}
    (hpt : ∀ (y : Vec d) (i j : Fin d), Measurable (fun a => F a y i j))
    (hgen : ∀ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ →
      Measurable (fun a => entryTestR i j φ (F a))) :
    Measurable F :=
  measurable_into_sup
    (measurable_into_pointwiseSigmaR (measurable_toFun_of_entries hpt))
    (measurable_into_entryTestSigmaR hgen)

/-- Scalar entry evaluation is measurable for the canonical σ-algebra (pointwise
information is recovered from the pointwise lane). -/
theorem measurable_apply_entry (y : Vec d) (i j : Fin d) :
    Measurable (fun a : RegCoeffField d => a y i j) := by
  have htoFun : @Measurable (RegCoeffField d) (Vec d → Mat d) (pointwiseSigmaR d)
      MeasurableSpace.pi RegCoeffField.toFun := Measurable.of_comap_le le_rfl
  have hentry : Measurable (fun f : Vec d → Mat d => f y i j) :=
    ((measurable_pi_apply y).eval).eval
  exact (hentry.comp htoFun).mono (pointwiseSigmaR_le d) le_rfl

/-- The entry generator functional is measurable for the canonical σ-algebra. -/
theorem measurable_entryTestR (i j : Fin d) {φ : Vec d → ℝ} (hφ : IsProbeR φ) :
    Measurable (entryTestR i j φ) := by
  have h : @Measurable (RegCoeffField d) ℝ (entryTestSigmaR d) _ (entryTestR i j φ) := by
    intro t ht
    exact MeasurableSpace.measurableSet_generateFrom ⟨i, j, φ, hφ, t, ht, rfl⟩
  exact h.mono (entryTestSigmaR_le d) le_rfl

/-- **The local carrier σ-algebra is coarser than the canonical one.**  Each
generator of `LocalSigmaR U` is an entry-test preimage of a measurable set, hence
measurable for the canonical σ-algebra. -/
theorem LocalSigmaR_le (U : Set (Vec d)) :
    LocalSigmaR U ≤ instMeasurableSpaceRegCoeffField d := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨i, j, φ, hφ, _hsupp, t, ht, rfl⟩
  exact measurable_entryTestR i j hφ ht

/-! ## The crux: `MeasurableAdd₂` at the join -/

/-- **Addition is genuinely measurable at the join.**  Both lanes are handled by
additivity of their generators: the pointwise lane by coordinatewise additivity
of evaluations, the entry-test lane by `entryTestR_add`.  This is exactly what
fails on the raw junk-field space. -/
instance instMeasurableAdd₂ : MeasurableAdd₂ (RegCoeffField d) := by
  refine ⟨measurable_into_regCoeffField' ?_ ?_⟩
  · intro y i j
    have hfun : (fun p : RegCoeffField d × RegCoeffField d => (p.1 + p.2) y i j)
        = fun p => p.1 y i j + p.2 y i j := by
      funext p; simp only [RegCoeffField.add_apply, Matrix.add_apply]
    rw [hfun]
    exact ((measurable_apply_entry y i j).comp measurable_fst).add
      ((measurable_apply_entry y i j).comp measurable_snd)
  · intro i j φ hφ
    have hfun : (fun p : RegCoeffField d × RegCoeffField d => entryTestR i j φ (p.1 + p.2))
        = fun p => entryTestR i j φ p.1 + entryTestR i j φ p.2 :=
      funext fun p => entryTestR_add i j hφ p.1 p.2
    rw [hfun]
    exact ((measurable_entryTestR i j hφ).comp measurable_fst).add
      ((measurable_entryTestR i j hφ).comp measurable_snd)

/-! ## The layered builder (acceptance theorem) -/

/-- **The layered Superdiffusion builder is a genuinely measurable carrier-valued
map.**  Once addition is measurable at the join, a base field-map plus a finite
sum of measurable layer maps is measurable — no a.e. qualification needed. -/
theorem measurable_layeredBuilder {α ι : Type*} [MeasurableSpace α] {s : Finset ι}
    {base : α → RegCoeffField d} {A : ι → α → RegCoeffField d}
    (hbase : Measurable base) (hA : ∀ l ∈ s, Measurable (A l)) :
    Measurable (fun ω => base ω + ∑ l ∈ s, A l ω) :=
  hbase.add (Finset.measurable_sum s hA)

/-! ## Endomorphism transport -/

/-- The adjoint (entrywise transpose) is a carrier endomorphism. -/
def adjointReg (a : RegCoeffField d) : RegCoeffField d where
  toFun := fun x => (a x).transpose
  entry_measurable := fun i j => by
    simpa [Matrix.transpose_apply] using a.entry_measurable j i
  entry_locInt := fun i j => by
    simpa [Matrix.transpose_apply] using a.entry_locInt j i

@[simp] theorem adjointReg_apply (a : RegCoeffField d) (x : Vec d) :
    adjointReg a x = (a x).transpose := rfl

/-- Generator transport for the adjoint. -/
theorem entryTestR_adjointReg (i j : Fin d) (φ : Vec d → ℝ) (a : RegCoeffField d) :
    entryTestR i j φ (adjointReg a) = entryTestR j i φ a := by
  unfold entryTestR
  simp only [adjointReg_apply, Matrix.transpose_apply]

/-- **The adjoint is genuinely measurable at the join** — the model endomorphism,
measurable by generator transport in both lanes. -/
theorem measurable_adjointReg : Measurable (adjointReg (d := d)) := by
  refine measurable_into_regCoeffField' ?_ ?_
  · intro y i j
    have hfun : (fun a : RegCoeffField d => adjointReg a y i j)
        = fun a => a y j i := by
      funext a; simp only [adjointReg_apply, Matrix.transpose_apply]
    rw [hfun]; exact measurable_apply_entry y j i
  · intro i j φ hφ
    have hfun : (fun a : RegCoeffField d => entryTestR i j φ (adjointReg a))
        = fun a => entryTestR j i φ a := funext fun a => entryTestR_adjointReg i j φ a
    rw [hfun]; exact measurable_entryTestR j i hφ

/-- **General probe-transport criterion for endomorphisms.**  A self-map `T` of
the carrier is measurable at the join if every scalar entry of `T a` is a
measurable function of `a`, and each entry generator on `T a` equals a scalar
multiple of a (possibly relabelled) entry generator on `a`.  Translation,
rotation, adjoint and dilation all fit this pattern (the paper,
Armstrong–Kuusi–Loher, to appear). -/
theorem measurable_of_entryTestR_transport {T : RegCoeffField d → RegCoeffField d}
    (hpt : ∀ (y : Vec d) (i j : Fin d), Measurable (fun a => T a y i j))
    (htrans : ∀ (i j : Fin d) (φ : Vec d → ℝ), IsProbeR φ →
      ∃ (c : ℝ) (i' j' : Fin d) (ψ : Vec d → ℝ), IsProbeR ψ ∧
        ∀ a, entryTestR i j φ (T a) = c * entryTestR i' j' ψ a) :
    Measurable T := by
  refine measurable_into_regCoeffField' hpt ?_
  intro i j φ hφ
  obtain ⟨c, i', j', ψ, hψ, hEq⟩ := htrans i j φ hφ
  have hfun : (fun a => entryTestR i j φ (T a)) = fun a => c * entryTestR i' j' ψ a :=
    funext hEq
  rw [hfun]
  exact (measurable_entryTestR i' j' hψ).const_mul c

/-! ## Laws on the carrier -/

/-- A **law** on the carrier is a measure on `RegCoeffField d` (for the canonical
σ-algebra).  Packet P3 retargets `RestrictionCoeffLaw` to this type. -/
abbrev RegCoeffLaw (d : ℕ) := Measure (RegCoeffField d)

end

end Homogenization
