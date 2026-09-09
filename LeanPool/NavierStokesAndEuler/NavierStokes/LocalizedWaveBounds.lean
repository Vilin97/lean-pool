/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PeriodizedWaveBounds

@[expose] public section

/-!
# Wave bounds from primitive jets on native support cells

The background phase and its material defect are controlled only where
the native coefficient can be nonzero.  No extension of these controls to
the whole fast lift is required.
-/

noncomputable section

namespace NavierStokes.LocalizedWaveBounds

open Set Function Filter WeightedClasses HarmonicCalculus LinearWaveBounds
open scoped Topology ContDiff BigOperators InnerProductSpace

variable {D E F G I : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A local all-jet class. The extra index can contain both the spatial
label and the lattice copy, and the envelope may depend on that index.
Every constant precedes the band, label, copy, and evaluation point. -/
structure LocalClass (s : StripData D) (K : ℕ → I → Set D)
    (w : ℕ → I → D → ℝ) (α : ℝ) (f : ℕ → I → D → E) : Prop where
  weight_nonneg : ∀ n i x, x ∈ s.domain → 0 ≤ w n i x
  smooth : ∀ n i x, x ∈ s.domain → x ∈ K n i → ContDiffAt ℝ ∞ (f n i) x
  bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ n i x, x ∈ s.domain → x ∈ K n i → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f n i) x‖ ≤ majorant s (fun n x => w n i x) α C p n x

abbrev LocalWave (s : StripData D) (K : ℕ → I → Set D)
    (P : ℕ → I → D → ℝ) (α : ℝ) (f : ℕ → I → D → E) : Prop :=
  LocalClass s K (fun n i x => Real.sqrt (s.zeta x) * P n i x) α f

abbrev LocalUnweighted (s : StripData D) (K : ℕ → I → Set D)
    (α : ℝ) (f : ℕ → I → D → E) : Prop := LocalClass s K (fun _ _ _ => 1) α f

private theorem finite_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

private theorem bilinear_jet_at (L : E →L[ℝ] F →L[ℝ] G)
    {u : D → E} {v : D → F} {x : D} (hu : ContDiffAt ℝ ∞ u x)
    (hv : ContDiffAt ℝ ∞ v x) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {m j : ℕ} (hj : j ≤ m)
    (hbu : ∀ k ≤ m, ‖iteratedFDeriv ℝ k u x‖ ≤ A)
    (hbv : ∀ k ≤ m, ‖iteratedFDeriv ℝ k v x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun y => L (u y) (v y)) x‖ ≤ ‖L‖ * (2 : ℝ) ^ m * A * B := by
  obtain ⟨U, hU, huU⟩ := hu.contDiffOn (finite_le_infty j) (by simp)
  obtain ⟨V, hV, hvV⟩ := hv.contDiffOn (finite_le_infty j) (by simp)
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem hU hV)
  have hle := JetBounds.norm_iteratedFDeriv_bilinear_le_on L hO
    (huU.mono (hOsub.trans inter_subset_left))
    (hvV.mono (hOsub.trans inter_subset_right)) hxO (le_refl (j : WithTop ℕ∞))
  have hsum : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
      ‖iteratedFDeriv ℝ k u x‖ * ‖iteratedFDeriv ℝ (j - k) v x‖) ≤ (2 : ℝ) ^ m * A * B := by
    calc
      _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro k hk
        have hkj : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hbu k (hkj.trans hj)) (Nat.cast_nonneg _))
          (hbv (j - k) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = (2 : ℝ) ^ j * A * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hchoose : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hchoose]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB
  exact hle.trans (by
    calc
      _ ≤ ‖L‖ * ((2 : ℝ) ^ m * A * B) := mul_le_mul_of_nonneg_left hsum (norm_nonneg L)
      _ = _ := by ring)

namespace LocalClass

variable {s : StripData D} {K : ℕ → I → Set D} {w v : ℕ → I → D → ℝ}
  {α β : ℝ} {f g : ℕ → I → D → E}

theorem of_global {w0 : ℕ → D → ℝ} {f0 : ℕ → D → E}
    (hf : MemClass s w0 α f0) :
    LocalClass s K (fun n _ => w0 n) α (fun n _ => f0 n) :=
  ⟨fun n _ x hx => hf.weight_nonneg n x hx,
    fun n _ x hx _ => (hf.smooth n).contDiffAt (s.isOpen_domain.mem_nhds hx),
    fun m => by
      obtain ⟨C, hC, p, hb⟩ := hf.bounds m
      exact ⟨C, hC, p, fun n _ x hx _ j hj => hb n x hx j hj⟩⟩

theorem of_localJets {w0 : ℕ → D → ℝ}
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w0 n x)
    (hf : PeriodizedWaveBounds.LocalJets s w0 α K f) :
    LocalClass s K (fun n _ => w0 n) α f :=
  ⟨fun n _ x hx => hw n x hx, hf.smooth, hf.bounds⟩

theorem to_localJets {w0 : ℕ → D → ℝ}
    (hf : LocalClass s K (fun n _ => w0 n) α f) :
    PeriodizedWaveBounds.LocalJets s w0 α K f := ⟨hf.smooth, hf.bounds⟩

theorem congr_germ (hf : LocalClass s K w α f)
    (he : ∀ n i x, x ∈ s.domain → x ∈ K n i → f n i =ᶠ[𝓝 x] g n i) :
    LocalClass s K w α g := by
  refine ⟨hf.weight_nonneg, fun n i x hx hi =>
    (hf.smooth n i x hx hi).congr_of_eventuallyEq (he n i x hx hi).symm, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, fun n i x hx hi j hj => ?_⟩
  rw [← PeriodizedWaveBounds.jets_eq_of_germ (he n i x hx hi) j]
  exact hb n i x hx hi j hj

theorem congr (hf : LocalClass s K w α f) (he : ∀ n i x, f n i x = g n i x) :
    LocalClass s K w α g :=
  hf.congr_germ (fun n i _ _ _ => Filter.Eventually.of_forall (he n i))

/-- Enlarge only the set on which a supported output is estimated.
The input background need not have any estimate on the added points. -/
theorem enlarge {C : ℕ → I → Set D} (hf : LocalClass s C w α f)
    (hcover : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      x ∈ C n i ∨ f n i =ᶠ[𝓝 x] fun _ => 0) : LocalClass s K w α f := by
  refine ⟨hf.weight_nonneg, ?_, ?_⟩
  · intro n i x hx hi
    rcases hcover n i x hx hi with hC | hz
    · exact hf.smooth n i x hx hC
    · exact contDiffAt_const.congr_of_eventuallyEq hz
  · intro m
    obtain ⟨A, hA, p, hb⟩ := hf.bounds m
    refine ⟨A, hA, p, fun n i x hx hi j hj => ?_⟩
    rcases hcover n i x hx hi with hC | hz
    · exact hb n i x hx hC j hj
    · rw [PeriodizedWaveBounds.jets_eq_of_germ hz j]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using
        majorant_nonneg s (fun n x => w n i x) α hA p n x (hf.weight_nonneg n i x hx)

theorem map (hf : LocalClass s K w α f) (L : E →L[ℝ] F) :
    LocalClass s K w α (fun n i x => L (f n i x)) := by
  refine ⟨hf.weight_nonneg, fun n i x hx hi =>
    L.contDiff.contDiffAt.comp x (hf.smooth n i x hx hi), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, p, fun n i x hx hi j hj => ?_⟩
  change ‖iteratedFDeriv ℝ j (L ∘ f n i) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left ((hf.smooth n i x hx hi).of_le (finite_le_infty j)) le_rfl]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (f n i) x‖ := L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L‖ * majorant s (fun n x => w n i x) α C p n x :=
      mul_le_mul_of_nonneg_left (hb n i x hx hi j hj) (norm_nonneg _)
    _ = _ := by unfold majorant; ring

theorem mono_exponent (hf : LocalClass s K w α f) (hβα : β ≤ α) :
    LocalClass s K w β f := by
  refine ⟨hf.weight_nonneg, hf.smooth, fun m => ?_⟩
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, fun n i x hx hi j hj => (hb n i x hx hi j hj).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (hf.weight_nonneg n i x hx)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (s.growth_nonneg n x) p)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (s.epsilon_pos n) (s.epsilon_le_one n) hβα) hC

theorem mono_weight (hf : LocalClass s K w α f)
    (hv : ∀ n i x, x ∈ s.domain → 0 ≤ v n i x)
    (hwv : ∀ n i x, x ∈ s.domain → x ∈ K n i → w n i x ≤ v n i x) :
    LocalClass s K v α f := by
  refine ⟨hv, hf.smooth, fun m => ?_⟩
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, fun n i x hx hi j hj => (hb n i x hx hi j hj).trans ?_⟩
  apply mul_le_mul_of_nonneg_left (hwv n i x hx hi)
  exact mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)
    (pow_nonneg (s.growth_nonneg n x) p)

theorem add (hf : LocalClass s K w α f) (hg : LocalClass s K w α g) :
    LocalClass s K w α (fun n i x => f n i x + g n i x) := by
  refine ⟨hf.weight_nonneg, fun n i x hx hi =>
    (hf.smooth n i x hx hi).add (hg.smooth n i x hx hi), fun m => ?_⟩
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hg.bounds m
  refine ⟨A + B, add_nonneg hA hB, p + q, fun n i x hx hi j hj => ?_⟩
  rw [fun_iteratedFDeriv_add_apply ((hf.smooth n i x hx hi).of_le (finite_le_infty j))
    ((hg.smooth n i x hx hi).of_le (finite_le_infty j))]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f n i) x‖ + ‖iteratedFDeriv ℝ j (g n i) x‖ := norm_add_le _ _
    _ ≤ majorant s (fun n x => w n i x) α A p n x +
        majorant s (fun n x => w n i x) α B q n x :=
      add_le_add (ha n i x hx hi j hj) (hb n i x hx hi j hj)
    _ ≤ majorant s (fun n x => w n i x) α A (p + q) n x +
        majorant s (fun n x => w n i x) α B (p + q) n x :=
      add_le_add (majorant_mono_degree s _ α hA (Nat.le_add_right _ _) n x (hf.weight_nonneg n i x
        hx))
        (majorant_mono_degree s _ α hB (Nat.le_add_left _ _) n x (hf.weight_nonneg n i x hx))
    _ = _ := by unfold majorant; ring

theorem neg (hf : LocalClass s K w α f) : LocalClass s K w α (fun n i x => -f n i x) := by
  simpa only [_root_.neg_apply, ContinuousLinearMap.id_apply] using
    hf.map (-ContinuousLinearMap.id ℝ E)

theorem sub (hf : LocalClass s K w α f) (hg : LocalClass s K w α g) :
    LocalClass s K w α (fun n i x => f n i x - g n i x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem zero (hw : ∀ n i x, x ∈ s.domain → 0 ≤ w n i x) :
    LocalClass s K w α (fun _ _ _ => (0 : E)) := by
  refine ⟨hw, fun _ _ _ _ _ => contDiffAt_const, fun m => ⟨0, le_rfl, 0, ?_⟩⟩
  intro n i x hx hi j hj
  simp [majorant]

theorem fderiv (hf : LocalClass s K w α f) :
    LocalClass s K w α (fun n i => _root_.fderiv ℝ (f n i)) := by
  refine ⟨hf.weight_nonneg, fun n i x hx hi => (hf.smooth n i x hx hi).fderiv_right (by simp),
    fun m => ?_⟩
  obtain ⟨C, hC, p, hb⟩ := hf.bounds (m + 1)
  refine ⟨C, hC, p, fun n i x hx hi j hj => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact hb n i x hx hi (j + 1) (Nat.add_le_add_right hj 1)

theorem directional (hf : LocalClass s K w α f) (e : D) :
    LocalClass s K w α (fun n i x => _root_.fderiv ℝ (f n i) x e) :=
  hf.fderiv.map (ContinuousLinearMap.apply ℝ E e)

theorem bilinear {u : ℕ → I → D → F} (hf : LocalClass s K w α f)
    (hu : LocalClass s K v β u) (L : E →L[ℝ] F →L[ℝ] G) :
    LocalClass s K (fun n i x => w n i x * v n i x) (α + β)
      (fun n i x => L (f n i x) (u n i x)) := by
  refine ⟨fun n i x hx => mul_nonneg (hf.weight_nonneg n i x hx) (hu.weight_nonneg n i x hx),
    fun n i x hx hi => (L.contDiff.contDiffAt.comp x (hf.smooth n i x hx hi)).clm_apply
      (hu.smooth n i x hx hi), fun m => ?_⟩
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hu.bounds m
  refine ⟨‖L‖ * (2 : ℝ) ^ m * A * B, by positivity, p + q, fun n i x hx hi j hj => ?_⟩
  calc
    _ ≤ ‖L‖ * (2 : ℝ) ^ m * majorant s (fun n x => w n i x) α A p n x *
        majorant s (fun n x => v n i x) β B q n x :=
      bilinear_jet_at L (hf.smooth n i x hx hi) (hu.smooth n i x hx hi)
        (majorant_nonneg s _ α hA p n x (hf.weight_nonneg n i x hx))
        (majorant_nonneg s _ β hB q n x (hu.weight_nonneg n i x hx)) hj
        (fun k hk => ha n i x hx hi k hk) (fun k hk => hb n i x hx hi k hk)
    _ = (‖L‖ * (2 : ℝ) ^ m) *
        (majorant s (fun n x => w n i x) α A p n x * majorant s (fun n x => v n i x) β B q n x) :=
          by ring
    _ = _ := by rw [majorant_mul]; unfold majorant; ring

theorem smul {r : ℕ → I → D → ℝ} (hr : LocalClass s K v β r)
    (hf : LocalClass s K w α f) :
    LocalClass s K (fun n i x => v n i x * w n i x) (β + α)
      (fun n i x => r n i x • f n i x) :=
  hr.bilinear hf (ContinuousLinearMap.lsmul ℝ ℝ)

theorem mul {a b : ℕ → I → D → ℝ} (ha : LocalClass s K w α a)
    (hb : LocalClass s K v β b) :
    LocalClass s K (fun n i x => w n i x * v n i x) (α + β)
      (fun n i x => a n i x * b n i x) := by
  simpa only [smul_eq_mul] using ha.smul hb

theorem band_smul {r : ℕ → ℝ} (hf : LocalClass s K w α f)
    (hr : BandBound s β r) :
    LocalClass s K w (α + β) (fun n i x => r n • f n i x) := by
  have hc : UnweightedClass s β (fun n (_ : D) => r n) := by
    simpa only [smul_eq_mul, mul_one, zero_add] using (unweighted_const s (1 : ℝ)).band_smul hr
  simpa only [one_mul, add_comm β α] using (LocalClass.of_global hc (K := K)).smul hf

theorem band_const {r : ℕ → ℝ} (hr : BandBound s β r) :
    LocalUnweighted s K β (fun n _ (_ : D) => r n) := by
  have hc : UnweightedClass s β (fun n (_ : D) => r n) := by
    simpa only [smul_eq_mul, mul_one, zero_add] using (unweighted_const s (1 : ℝ)).band_smul hr
  exact LocalClass.of_global hc

end LocalClass

section ElementaryOperations

variable {s : StripData D} {K : ℕ → I → Set D} {w : ℕ → I → D → ℝ} {α β : ℝ}

theorem unweighted_mul {a b : ℕ → I → D → ℝ} (ha : LocalUnweighted s K α a)
    (hb : LocalUnweighted s K β b) :
    LocalUnweighted s K (α + β) (fun n i x => a n i x * b n i x) := by
  simpa only [mul_one] using ha.mul hb

theorem unweighted_smul {a : ℕ → I → D → ℝ} {f : ℕ → I → D → E}
    (ha : LocalUnweighted s K α a) (hf : LocalClass s K w β f) :
    LocalClass s K w (α + β) (fun n i x => a n i x • f n i x) := by
  simpa only [one_mul] using ha.smul hf

theorem real_mul_complex {a : ℕ → I → D → ℝ} {f : ℕ → I → D → ℂ}
    (ha : LocalUnweighted s K α a) (hf : LocalClass s K w β f) :
    LocalClass s K w (α + β) (fun n i x => (a n i x : ℂ) * f n i x) := by
  simpa only [Complex.real_smul] using unweighted_smul ha hf

theorem complex_mul_real {f : ℕ → I → D → ℂ} {a : ℕ → I → D → ℝ}
    (hf : LocalClass s K w α f) (ha : LocalUnweighted s K β a) :
    LocalClass s K w (α + β) (fun n i x => f n i x * (a n i x : ℂ)) := by
  simpa only [mul_comm, add_comm] using real_mul_complex ha hf

theorem constant_complex_mul {f : ℕ → I → D → ℂ} (hf : LocalClass s K w α f) (c : ℂ) :
    LocalClass s K w α (fun n i x => c * f n i x) := by
  simpa using hf.map (c • ContinuousLinearMap.id ℝ ℂ)

theorem constant_real_mul {f : ℕ → I → D → ℝ} (hf : LocalClass s K w α f) (c : ℝ) :
    LocalClass s K w α (fun n i x => c * f n i x) := by
  simpa using hf.map (c • ContinuousLinearMap.id ℝ ℝ)

theorem local_const (c : E) : LocalUnweighted s K 0 (fun _ _ _ => c) :=
  LocalClass.of_global (unweighted_const s c)

theorem component_classes {f : ℕ → I → D → ComplexVector}
    (hf : ∀ j : Fin 3, LocalClass s K w α (fun n i x => f n i x j)) :
    LocalClass s K w α f := by
  have h0 := (hf 0).map (LinearWaveBounds.insertComponent 0)
  have h1 := (hf 1).map (LinearWaveBounds.insertComponent 1)
  have h2 := (hf 2).map (LinearWaveBounds.insertComponent 2)
  apply ((h0.add h1).add h2).congr
  intro n i x
  ext j
  fin_cases j <;> simp [LinearWaveBounds.insertComponent]

theorem angular_classes {f : ℕ → I → D → ComplexVector}
    (hf : ∀ j, LocalClass s K w α (fun n i x => f n i x j)) :
    ∀ j, LocalClass s K w α (fun n i x => angularGenerator (f n i x) j) := by
  intro j
  fin_cases j
  · simpa [angularGenerator] using (hf 1).neg
  · simpa [angularGenerator] using hf 0
  · simpa [angularGenerator] using (LocalClass.zero (α := α) (E := ℂ) (hf 0).weight_nonneg)

end ElementaryOperations

section Derivatives

variable {s : StripData D} {K : ℕ → I → Set D} {w : ℕ → I → D → ℝ}
  {α κ : ℝ}

noncomputable def Dr (d : GraphDirections D) (f : ℕ → I → D → E) : ℕ → I → D → E :=
  fun n i => along (d.radialField n) (f n i)

noncomputable def Dz (d : GraphDirections D) (s : StripData D) (f : ℕ → I → D → E) :
    ℕ → I → D → E := fun n i => along (d.axialField s n) (f n i)

noncomputable def Dt (d : GraphDirections D) (f : ℕ → I → D → E) : ℕ → I → D → E :=
  fun n i => along (fun _ => d.slow) (f n i)

noncomputable def Dfast (d : GraphDirections D) (f : ℕ → I → D → E) : ℕ → I → D → E :=
  fun n i => along (d.fastField n) (f n i)

theorem Dr_mem (d : GraphDirections D) {f : ℕ → I → D → E} (hf : LocalClass s K w α f)
    (hρ : LocalUnweighted s K 0 (fun _ _ => d.radialProfile))
    (hM : BandBound s (-κ) d.radialScale) (hκ : 0 ≤ κ) :
    LocalClass s K w (α - κ) (Dr d f) := by
  have he := (hf.directional d.radial).mono_exponent (sub_le_self α hκ)
  have hv := (unweighted_smul hρ (hf.directional d.auxiliary)).band_smul hM
  have hv' : LocalClass s K w (α - κ) (fun n i x =>
      d.radialScale n • (d.radialProfile x • fderiv ℝ (f n i) x d.auxiliary)) := by
    simpa only [zero_add, sub_eq_add_neg] using hv
  apply (he.add hv').congr
  intro n i x
  simp [Dr, GraphDirections.radialField, along]

theorem Dz_mem (d : GraphDirections D) {f : ℕ → I → D → E} (hf : LocalClass s K w α f) :
    LocalClass s K w (α + 1) (Dz d s f) := by
  have hh := (hf.directional d.axial).band_smul (LinearWaveBounds.band_epsilon s)
  unfold Dz GraphDirections.axialField along
  simpa only [map_smul] using hh

theorem Dt_mem (d : GraphDirections D) {f : ℕ → I → D → E} (hf : LocalClass s K w α f) :
    LocalClass s K w α (Dt d f) := hf.directional d.slow

theorem Dfast_mem (d : GraphDirections D) {f : ℕ → I → D → E} (hf : LocalClass s K w α f)
    (hfast : BandBound s 0 d.fastScale) : LocalClass s K w α (Dfast d f) := by
  unfold Dfast GraphDirections.fastField along
  simpa only [map_smul, add_zero] using
    (hf.directional d.fast).band_smul hfast

theorem Dr_base_mem (d : GraphDirections D) {f : ℕ → I → D → E} (hf : LocalClass s K w α f)
    (haux : ∀ n i x, x ∈ s.domain → x ∈ K n i →
      (fun y => fderiv ℝ (f n i) y d.auxiliary) =ᶠ[𝓝 x] fun _ => 0) :
    LocalClass s K w α (Dr d f) := by
  apply (hf.directional d.radial).congr_germ
  intro n i x hx hi
  filter_upwards [haux n i x hx hi] with y hy
  simp [Dr, GraphDirections.radialField, along, hy]

end Derivatives

namespace LocalClass

variable {s : StripData D} {K : ℕ → I → Set D}

/-- Only the outer function is bounded on a compact set. The inner jets
are used at the native support point, never on the whole strip. -/
theorem compact_comp {f : ℕ → I → D → E} (hf : LocalUnweighted s K 0 f)
    {g : E → F} {U Cset : Set E} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hCset : IsCompact Cset) (hCU : Cset ⊆ U)
    (hmap : ∀ n i x, x ∈ s.domain → x ∈ K n i → f n i x ∈ Cset) :
    LocalUnweighted s K 0 (fun n i x => g (f n i x)) := by
  refine ⟨fun _ _ _ _ => zero_le_one, fun n i x hx hi =>
    (hg.contDiffAt (hU.mem_nhds (hCU (hmap n i x hx hi)))).comp x
      (hf.smooth n i x hx hi), fun m => ?_⟩
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨C, hC, hc⟩ := PhaseJetBounds.compact_jet_bound hU hg hCset hCU m
  let B := max 1 A
  have hB : 1 ≤ B := le_max_left _ _
  have hAB : A ≤ B := le_max_right _ _
  refine ⟨(m.factorial : ℝ) * C * B ^ m, by positivity, p * m, fun n i x hx hi j hj => ?_⟩
  have hD : 1 ≤ B * s.growth n x ^ p :=
    one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ (s.one_le_growth n x))
  have hjet (k : ℕ) (hk : k ≤ m) :
      ‖iteratedFDeriv ℝ k (f n i) x‖ ≤ B * s.growth n x ^ p := by
    have hb := ha n i x hx hi k hk
    simp only [majorant, Real.rpow_zero, mul_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hAB (pow_nonneg (s.growth_nonneg n x) p))
  obtain ⟨V, hV, hfV⟩ := (hf.smooth n i x hx hi).contDiffOn (finite_le_infty j) (by simp)
  have hfu : ∀ᶠ y in 𝓝 x, f n i y ∈ U :=
    (hf.smooth n i x hx hi).continuousAt.eventually (hU.mem_nhds (hCU (hmap n i x hx hi)))
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem hV hfu)
  have hfO := hfV.mono (hOsub.trans inter_subset_left)
  have hmapO : MapsTo (f n i) O U := fun _ hy => (hOsub hy).2
  have hb := norm_iteratedFDerivWithin_comp_le (hg.of_le (finite_le_infty j)) hfO
    (le_refl (j : WithTop ℕ∞)) hU.uniqueDiffOn hO.uniqueDiffOn hmapO hxO
    (C := C) (D := B * s.growth n x ^ p) (fun k hk => ?_) (fun k hk hkj => ?_)
  · rw [iteratedFDerivWithin_of_isOpen j hO hxO] at hb
    change ‖iteratedFDeriv ℝ j (g ∘ f n i) x‖ ≤ _
    calc
      _ ≤ (j.factorial : ℝ) * C * (B * s.growth n x ^ p) ^ j := hb
      _ ≤ (m.factorial : ℝ) * C * (B * s.growth n x ^ p) ^ m := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast Nat.factorial_le hj) (zero_le_one.trans hC)
        · exact pow_le_pow_right₀ hD hj
        · positivity
        · positivity
      _ = _ := by simp only [majorant, Real.rpow_zero, mul_one, mul_pow, ← pow_mul]; ring
  · rw [iteratedFDerivWithin_of_isOpen k hU (hCU (hmap n i x hx hi))]
    exact hc k (hk.trans hj) (f n i x) (hmap n i x hx hi)
  · rw [iteratedFDerivWithin_of_isOpen k hO hxO]
    exact (hjet k (hkj.trans hj)).trans (by simpa using pow_le_pow_right₀ hD hk)

theorem inv {f : ℕ → I → D → ℝ} (hf : LocalUnweighted s K 0 f)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ |f n i x|)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ K n i → |f n i x| ≤ M) :
    LocalUnweighted s K 0 (fun n i x => (f n i x)⁻¹) := by
  let Cset : Set ℝ := Metric.closedBall 0 M ∩ {r | b ≤ |r|}
  have hCset : IsCompact Cset := (isCompact_closedBall 0 M).inter_right
    (isClosed_le continuous_const continuous_abs)
  have hCU : Cset ⊆ {r : ℝ | r ≠ 0} := by
    intro r hr he
    have h : b ≤ |r| := hr.2
    simp only [he, abs_zero] at h
    linarith
  apply hf.compact_comp isClosed_singleton.isOpen_compl
    (contDiffOn_id.inv (fun _ h => h)) hCset hCU
  intro n i x hx hi
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hupper n i
    x hx hi,
    hlower n i x hx hi⟩

end LocalClass

/-! ## The same wave algebra with a uniform extra index -/

structure WaveFamily (D I : Type*) where
  radius : ℕ → I → D → ℝ
  radialBase : ℕ → I → D → ℝ
  frequencyBase : ℕ → I → D → ℝ
  axialBase : ℕ → I → D → ℝ
  phase : ℕ → I → D → ℝ
  amplitude : ℕ → I → D → ComplexVector
  pressure : ℕ → I → D → ℂ
  frequency : ℕ → I → ℝ

namespace WaveFamily

noncomputable def coefficients (a : WaveFamily D I) (i : I) : WaveCoefficients D where
  radius n := a.radius n i
  radialBase n := a.radialBase n i
  frequencyBase n := a.frequencyBase n i
  axialBase n := a.axialBase n i
  phase n := a.phase n i
  amplitude n := a.amplitude n i
  pressure n := a.pressure n i
  frequency n := a.frequency n i

noncomputable def ofCoefficients (a : I → WaveCoefficients D) : WaveFamily D I where
  radius n i := (a i).radius n
  radialBase n i := (a i).radialBase n
  frequencyBase n i := (a i).frequencyBase n
  axialBase n i := (a i).axialBase n
  phase n i := (a i).phase n
  amplitude n i := (a i).amplitude n
  pressure n i := (a i).pressure n
  frequency n i := (a i).frequency n

noncomputable def normal (a : WaveFamily D I) (s : StripData D) (d : GraphDirections D) :
    ℕ → I → D → ProblemStatement.Space := fun n i => (a.coefficients i).normal s d n

noncomputable def defect (a : WaveFamily D I) (s : StripData D) (d : GraphDirections D) :
    ℕ → I → D → ℝ := fun n i => (a.coefficients i).defect s d n

noncomputable def remainder (a : WaveFamily D I) (s : StripData D) (d : GraphDirections D) :
    ℕ → I → D → ComplexVector := fun n i => (a.coefficients i).remainder s d n

noncomputable def principalVelocity (a : WaveFamily D I) (s : StripData D) (d : GraphDirections D)
    (f : ℕ → I → D → ComplexVector) : ℕ → I → D → ComplexVector :=
  fun n i => (a.coefficients i).principalVelocity s d (fun n => f n i) n

noncomputable def curlCorrection (a : WaveFamily D I) (s : StripData D) (d : GraphDirections D) :
    ℕ → I → D → ComplexVector := fun n i => (a.coefficients i).curlCorrection s d n

noncomputable def addAmplitude (a : WaveFamily D I) (f : ℕ → I → D → ComplexVector) : WaveFamily D
  I :=
  { a with amplitude := fun n i x => a.amplitude n i x + f n i x }

noncomputable def withCutoff (a : WaveFamily D I) (ψ : ℕ → I → D → ℝ) : WaveFamily D I :=
  { a with
    amplitude := fun n i x => ψ n i x • a.amplitude n i x
    pressure := fun n i x => (ψ n i x : ℂ) * a.pressure n i x }

noncomputable def retainedGood (a : WaveFamily D I) (s : StripData D) (d : GraphDirections D) :
    ℕ → I → D → ComplexVector := fun n i x =>
  a.principalVelocity s d (a.curlCorrection s d) n i x +
    (a.addAmplitude (a.curlCorrection s d)).remainder s d n i x

/-- Outside the complete input support, all the derived coefficients
vanish as germs, even if the background has no estimates there. -/
theorem outputs_zero_germs {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : WaveFamily D I) (s : StripData D) (d : GraphDirections D)
    {n : ℕ} {i : I} {x : D}
    (ha : a.amplitude n i =ᶠ[𝓝 x] fun _ => 0)
    (hp : a.pressure n i =ᶠ[𝓝 x] fun _ => 0) :
    (a.curlCorrection s d n i =ᶠ[𝓝 x] fun _ => 0) ∧
    ((a.addAmplitude (a.curlCorrection s d)).amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.retainedGood s d n i =ᶠ[𝓝 x] fun _ => 0) := by
  have hc : a.curlCorrection s d n i =ᶠ[𝓝 x] fun _ => 0 := by
    have hh := PeriodizedWaveBounds.curlCorrection_germ ha
      (a.frequency n i) (a.radius n i) (a.phase n i)
      (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    simp only [PeriodizedWaveBounds.coefficient_zero, PeriodizedWaveBounds.curlRemainder_zero] at hh
    exact hh
  have hcor : (a.addAmplitude (a.curlCorrection s d)).amplitude n i =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [ha, hc] with y hay hcy
    simp only [addAmplitude, hay, hcy, add_zero]
  have hpr : a.principalVelocity s d (a.curlCorrection s d) n i =ᶠ[𝓝 x] fun _ => 0 := by
    have hh := PeriodizedWaveBounds.principal_germ hc
      (Filter.EventuallyEq.refl (𝓝 x) (fun _ : D => (0 : ℂ)))
      (s.epsilon n) (a.frequency n i) (a.radius n i) (a.frequencyBase n i)
      (a.axialBase n i) (a.phase n i) (d.radialField n) (fun _ => d.angular)
      (d.axialField s n) (d.fastField n)
    simp only [PeriodizedWaveBounds.principal_zero] at hh
    exact hh
  have hr : (a.addAmplitude (a.curlCorrection s d)).remainder s d n i =ᶠ[𝓝 x] fun _ => 0 := by
    have hh := PeriodizedWaveBounds.remainder_germ hcor hp
      (s.epsilon n) (a.frequency n i) (a.radius n i) (a.radialBase n i)
      (a.frequencyBase n i) (a.axialBase n i) (a.phase n i) (d.radialField n)
      (fun _ => d.angular) (d.axialField s n) (d.fastField n) (fun _ => d.slow)
    simp only [PeriodizedWaveBounds.remainder_zero] at hh
    exact hh
  refine ⟨hc, hcor, ?_⟩
  filter_upwards [hpr, hr] with y hpy hry
  simp only [retainedGood, hpy, hry, add_zero]

/-- Containment of the two closed input supports is enough to supply
the local-estimate/zero-germ alternative; no output support is assumed. -/
theorem input_germ_cover_of_tsupport {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (a : WaveFamily D I) {C : ℕ → I → Set D}
    (ha : ∀ n i, tsupport (a.amplitude n i) ⊆ C n i)
    (hp : ∀ n i, tsupport (a.pressure n i) ⊆ C n i) (n : ℕ) (i : I) (x : D) :
    x ∈ C n i ∨ (a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧
      (a.pressure n i =ᶠ[𝓝 x] fun _ => 0) := by
  classical
  by_cases hx : x ∈ C n i
  · exact Or.inl hx
  · exact Or.inr ⟨PeriodizedWaveBounds.zero_germ_of_support isClosed_closure subset_closure
      (fun hi => hx (ha n i hi)),
      PeriodizedWaveBounds.zero_germ_of_support isClosed_closure subset_closure
      (fun hi => hx (hp n i hi))⟩

end WaveFamily

/-- Primitive local hypotheses. The normal and the material defect are
the actual expressions computed from the phase; their bounds are imposed
only on the native cells. Auxiliary independence is a local identity. -/
structure InputBounds (s : StripData D) (K : ℕ → I → Set D)
    (P : ℕ → I → D → ℝ) (α κ : ℝ) (d : GraphDirections D) (a : WaveFamily D I) : Prop where
  loss_nonneg : 0 ≤ κ
  radial_profile : LocalUnweighted s K 0 (fun _ _ => d.radialProfile)
  radial_scale : BandBound s (-κ) d.radialScale
  fast_scale : BandBound s 0 d.fastScale
  frequency_scale : LocalUnweighted s K (-(1 / 2 : ℝ)) (fun n i _ => a.frequency n i)
  radius : LocalUnweighted s K 0 a.radius
  inverse_radius : LocalUnweighted s K 0 (fun n i x => (a.radius n i x)⁻¹)
  radial_base : LocalUnweighted s K 1 a.radialBase
  frequency_base : LocalUnweighted s K 0 a.frequencyBase
  axial_base : LocalUnweighted s K 0 a.axialBase
  radial_base_aux : ∀ n i x, x ∈ s.domain → x ∈ K n i →
    (fun y => fderiv ℝ (a.radialBase n i) y d.auxiliary) =ᶠ[𝓝 x] fun _ => 0
  frequency_base_aux : ∀ n i x, x ∈ s.domain → x ∈ K n i →
    (fun y => fderiv ℝ (a.frequencyBase n i) y d.auxiliary) =ᶠ[𝓝 x] fun _ => 0
  axial_base_aux : ∀ n i x, x ∈ s.domain → x ∈ K n i →
    (fun y => fderiv ℝ (a.axialBase n i) y d.auxiliary) =ᶠ[𝓝 x] fun _ => 0
  normal : LocalUnweighted s K 0 (a.normal s d)
  defect : LocalUnweighted s K 1 (a.defect s d)
  amplitude : ∀ j, LocalWave s K P α (fun n i x => a.amplitude n i x j)
  pressure : LocalWave s K P (α + 1 / 2) a.pressure

theorem frequency_mul {s : StripData D} {K : ℕ → I → Set D} {w : ℕ → I → D → ℝ}
    {α : ℝ} {f : ℕ → I → D → ℂ} {freq : ℕ → I → ℝ}
    (hf : LocalClass s K w α f)
    (hk : LocalUnweighted s K (-(1 / 2 : ℝ)) (fun n i _ => freq n i)) :
    LocalClass s K w (α - 1 / 2) (fun n i x => phaseFactor (freq n i) * f n i x) := by
  have hh := constant_complex_mul (real_mul_complex hk hf) Complex.I
  simpa only [phaseFactor, mul_assoc, mul_left_comm, sub_eq_add_neg, add_comm α] using hh

namespace InputBounds

variable {s : StripData D} {K : ℕ → I → Set D} {P : ℕ → I → D → ℝ} {α κ : ℝ}
  {d : GraphDirections D} {a : WaveFamily D I}

theorem normal_component (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalUnweighted s K 0 (fun n i x => a.normal s d n i x j) :=
  h.normal.map (EuclideanSpace.proj j)

theorem inverse_radius_sq (h : InputBounds s K P α κ d a) :
    LocalUnweighted s K 0 (fun n i x => ((a.radius n i x) ^ 2)⁻¹) := by
  simpa only [zero_add, pow_two, mul_inv_rev] using unweighted_mul h.inverse_radius h.inverse_radius

theorem base_components (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalUnweighted s K 0 (fun n i x =>
      LinearWaveResidual.base (a.radius n i) (a.radialBase n i)
        (a.frequencyBase n i) (a.axialBase n i) x j) := by
  fin_cases j
  · simpa [LinearWaveResidual.base] using h.radial_base.mono_exponent (by norm_num : (0 : ℝ) ≤ 1)
  · simpa [LinearWaveResidual.base] using unweighted_mul h.radius h.frequency_base
  · simpa [LinearWaveResidual.base] using h.axial_base

theorem slowTransport_mem (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - 3 * κ) (fun n i x =>
      LinearWaveResidual.slowTransport (s.epsilon n) (a.radialBase n i) (a.axialBase n i)
        (fun _ => d.slow) (d.radialField n) (d.axialField s n) (a.amplitude n i) x j) := by
  have ht := ((Dt_mem d (h.amplitude j)).band_smul (LinearWaveBounds.band_epsilon s)).neg
  have hr := real_mul_complex h.radial_base
    (Dr_mem d (h.amplitude j) h.radial_profile h.radial_scale h.loss_nonneg)
  have hz := real_mul_complex h.axial_base (Dz_mem d (h.amplitude j))
  have ht' := ht.mono_exponent (show α + 1 / 2 - 3 * κ ≤ α + 1 by linarith [h.loss_nonneg])
  have hr' := hr.mono_exponent (show α + 1 / 2 - 3 * κ ≤ 1 + (α - κ) by linarith [h.loss_nonneg])
  have hz' := hz.mono_exponent (show α + 1 / 2 - 3 * κ ≤ 0 + (α + 1) by linarith [h.loss_nonneg])
  simpa only [LinearWaveResidual.slowTransport, Dt, Dr, Dz, Complex.real_smul, neg_mul]
    using (ht'.add hr').add hz'

theorem phaseDefect_mem (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - 3 * κ) (fun n i x =>
      phaseFactor (a.frequency n i) * Complex.ofReal (a.defect s d n i x) * a.amplitude n i x j) :=
        by
  have hh := frequency_mul (real_mul_complex h.defect (h.amplitude j)) h.frequency_scale
  have hh' := hh.mono_exponent
    (show α + 1 / 2 - 3 * κ ≤ (1 + α) - 1 / 2 by linarith [h.loss_nonneg])
  simpa only [mul_assoc] using hh'

theorem baseDerivativeRemainder_mem (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - 3 * κ) (fun n i x =>
      LinearWaveResidual.baseDerivativeRemainder (a.radius n i) (a.radialBase n i)
        (a.frequencyBase n i) (a.axialBase n i) (d.radialField n) (d.axialField s n)
        (a.amplitude n i) x j) := by
  have hbr := Dr_base_mem d h.radial_base h.radial_base_aux
  have h0 := (complex_mul_real (h.amplitude 0) hbr).mono_exponent
    (show α + 1 / 2 - 3 * κ ≤ α + 1 by linarith [h.loss_nonneg])
  have hbinv := unweighted_mul h.radial_base h.inverse_radius
  have h1 := (real_mul_complex hbinv (h.amplitude 1)).mono_exponent
    (show α + 1 / 2 - 3 * κ ≤ (1 + 0) + α by linarith [h.loss_nonneg])
  have hz (k : Fin 3) := (complex_mul_real (h.amplitude 2) (Dz_mem d (h.base_components
    k))).mono_exponent
    (show α + 1 / 2 - 3 * κ ≤ α + (0 + 1) by linarith [h.loss_nonneg])
  fin_cases j
  · simpa [LinearWaveResidual.baseDerivativeRemainder, Dr, Dz] using h0.add (hz 0)
  · simpa [LinearWaveResidual.baseDerivativeRemainder, Dz, div_eq_mul_inv] using h1.add (hz 1)
  · simpa [LinearWaveResidual.baseDerivativeRemainder, Dz] using hz 2

theorem pressureGradient_mem (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - 3 * κ) (fun n i x =>
      LinearWaveResidual.strippedPressureGradient (d.radialField n) (d.axialField s n)
        (a.pressure n i) x j) := by
  fin_cases j
  · have hh := (Dr_mem d h.pressure h.radial_profile h.radial_scale h.loss_nonneg).mono_exponent
      (show α + 1 / 2 - 3 * κ ≤ (α + 1 / 2) - κ by linarith [h.loss_nonneg])
    simp [LinearWaveResidual.strippedPressureGradient] at hh ⊢
    exact hh
  · simpa [LinearWaveResidual.strippedPressureGradient] using
      (LocalClass.zero (α := α + 1 / 2 - 3 * κ) (E := ℂ) (h.amplitude 0).weight_nonneg)
  · have hh := (Dz_mem d h.pressure).mono_exponent
      (show α + 1 / 2 - 3 * κ ≤ (α + 1 / 2) + 1 by linarith [h.loss_nonneg])
    simp [LinearWaveResidual.strippedPressureGradient] at hh ⊢
    exact hh

theorem viscousRemainder_mem (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α - 1 / 2 - 3 * κ) (fun n i x =>
      LinearWaveResidual.viscousRemainder (a.radius n i) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.frequency n i) (a.phase n i) (a.amplitude n i) x j) := by
  have hAi := h.amplitude j
  have hDr := Dr_mem d hAi h.radial_profile h.radial_scale h.loss_nonneg
  have hDrr := Dr_mem d hDr h.radial_profile h.radial_scale h.loss_nonneg
  have hDz := Dz_mem d hAi
  have hDzz := Dz_mem d hDz
  have hri := real_mul_complex h.inverse_radius hDr
  have hJ := angular_classes h.amplitude
  have hJJ := angular_classes hJ
  have hjj := real_mul_complex h.inverse_radius_sq (hJJ j)
  have hcrossr := real_mul_complex (h.normal_component 0) hDr
  have hcrossz := real_mul_complex (h.normal_component 2) hDz
  have hcrossr' : LocalWave s K P (α - κ) (fun n i x =>
      Complex.ofReal (a.normal s d n i x 0) * Dr d (fun n i x => a.amplitude n i x j) n i x) := by
    simpa only [zero_add] using hcrossr
  have hcrossz' := hcrossz.mono_exponent
    (show α - κ ≤ 0 + (α + 1) by linarith [h.loss_nonneg])
  have hcross := constant_complex_mul
    (frequency_mul (hcrossr'.add hcrossz') h.frequency_scale) 2
  have hNr := Dr_mem d (h.normal_component 0) h.radial_profile h.radial_scale h.loss_nonneg
  have hNi := unweighted_mul (h.normal_component 0) h.inverse_radius
  have hNz := Dz_mem d (h.normal_component 2)
  have hNr' : LocalUnweighted s K (-κ) (Dr d (fun n i x => a.normal s d n i x 0)) := by
    simpa only [zero_sub] using hNr
  have hNi' := hNi.mono_exponent (show -κ ≤ 0 + 0 by linarith [h.loss_nonneg])
  have hNz' := hNz.mono_exponent (show -κ ≤ 0 + 1 by linarith [h.loss_nonneg])
  have hdiv := frequency_mul (real_mul_complex ((hNr'.add hNi').add hNz') hAi) h.frequency_scale
  have htheta := constant_complex_mul
    (frequency_mul (real_mul_complex (unweighted_mul (h.normal_component 1) h.inverse_radius) (hJ
      j))
      h.frequency_scale) 2
  have hDrr' := hDrr.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ (α - κ) - κ by linarith [h.loss_nonneg])
  have hri' := hri.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ 0 + (α - κ) by linarith [h.loss_nonneg])
  have hDzz' := hDzz.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ (α + 1) + 1 by linarith [h.loss_nonneg])
  have hjj' := hjj.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ 0 + α by linarith [h.loss_nonneg])
  have hcross' := hcross.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ (α - κ) - 1 / 2 by linarith [h.loss_nonneg])
  have hdiv' := hdiv.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ (-κ + α) - 1 / 2 by linarith [h.loss_nonneg])
  have htheta' := htheta.mono_exponent
    (show α - 1 / 2 - 3 * κ ≤ ((0 + 0) + α) - 1 / 2 by linarith [h.loss_nonneg])
  have hh := (((((hDrr'.add hri').add hDzz').add hjj').add hcross').add hdiv').add htheta'
  simpa only [LinearWaveResidual.viscousRemainder, Dr, Dz, WaveFamily.normal,
    WaveFamily.coefficients, WaveCoefficients.normal, Complex.real_smul,
    div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, mul_assoc] using hh

theorem viscousPart_mem (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - 3 * κ) (fun n i x => (s.epsilon n : ℂ) *
      LinearWaveResidual.viscousRemainder (a.radius n i) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (a.frequency n i) (a.phase n i) (a.amplitude n i) x j) := by
  have hh := (h.viscousRemainder_mem j).band_smul (LinearWaveBounds.band_epsilon s)
  have he : (α - 1 / 2 - 3 * κ) + 1 = α + 1 / 2 - 3 * κ := by ring
  simpa only [he, Complex.real_smul] using hh

/-- Every actual term of the linear-wave remainder retains its stated
power, with constants uniform before every extra label and copy. -/
theorem remainder_components (h : InputBounds s K P α κ d a) (j : Fin 3) :
    LocalWave s K P (α + 1 / 2 - 3 * κ) (fun n i x => a.remainder s d n i x j) := by
  have hh := ((((h.slowTransport_mem j).add (h.phaseDefect_mem j)).add
    (h.baseDerivativeRemainder_mem j)).add (h.pressureGradient_mem j)).sub (h.viscousPart_mem j)
  simpa only [WaveFamily.remainder, WaveFamily.defect, WaveFamily.coefficients,
    WaveCoefficients.remainder, WaveCoefficients.defect, LinearWaveResidual.remainder] using hh

theorem remainder_class (h : InputBounds s K P α κ d a) :
    LocalWave s K P (α + 1 / 2 - 3 * κ) (a.remainder s d) :=
  component_classes h.remainder_components

theorem normal_norm_sq (h : InputBounds s K P α κ d a) :
    LocalUnweighted s K 0 (fun n i x => ‖a.normal s d n i x‖ ^ 2) := by
  have hh := h.normal.bilinear h.normal (innerSL ℝ)
  change LocalClass s K (fun _ _ _ => 1 * 1) (0 + 0)
    (fun n i x => ⟪a.normal s d n i x, a.normal s d n i x⟫_ℝ) at hh
  simpa only [mul_one, zero_add, real_inner_self_eq_norm_sq] using hh

theorem shear_mem (h : InputBounds s K P α κ d a) {β : ℝ}
    {f : ℕ → I → D → ComplexVector}
    (hf : ∀ j, LocalWave s K P β (fun n i x => f n i x j)) (j : Fin 3) :
    LocalWave s K P β (fun n i x =>
      LinearWaveResidual.shear (a.radius n i) (a.frequencyBase n i) (a.axialBase n i)
        (d.radialField n) (f n i) x j) := by
  have hFr := Dr_base_mem d h.frequency_base h.frequency_base_aux
  have hGr := Dr_base_mem d h.axial_base h.axial_base_aux
  have htheta : LocalUnweighted s K 0 (fun n i x =>
      2 * a.frequencyBase n i x + a.radius n i x * Dr d a.frequencyBase n i x) := by
    have hprod : LocalUnweighted s K 0 (fun n i x => a.radius n i x * Dr d a.frequencyBase n i x)
      := by
      simpa only [zero_add] using unweighted_mul h.radius hFr
    exact (constant_real_mul h.frequency_base 2).add hprod
  fin_cases j
  · simpa [LinearWaveResidual.shear, mul_assoc] using
      constant_complex_mul (real_mul_complex h.frequency_base (hf 1)) (-2)
  · have hh := real_mul_complex htheta (hf 0)
    simp only [LinearWaveResidual.shear,
      Dr, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, zero_add] at hh ⊢
    exact hh
  · simpa [LinearWaveResidual.shear, Dr] using real_mul_complex hGr (hf 0)

theorem principalVelocity_components (h : InputBounds s K P α κ d a) {β : ℝ}
    {f : ℕ → I → D → ComplexVector}
    (hf : ∀ j, LocalWave s K P β (fun n i x => f n i x j)) (j : Fin 3) :
    LocalWave s K P β (fun n i x => a.principalVelocity s d f n i x j) := by
  have hfast := Dfast_mem d (hf j) h.fast_scale
  have hK := h.shear_mem hf j
  have hn : LocalWave s K P β (fun n i x => (‖a.normal s d n i x‖ ^ 2 : ℝ) • f n i x j) := by
    simpa only [zero_add] using unweighted_smul h.normal_norm_sq (hf j)
  have hd := (unweighted_smul h.frequency_scale (unweighted_smul h.frequency_scale hn)).band_smul
    (LinearWaveBounds.band_epsilon s)
  have he : ((-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ) + β)) + 1 = β := by ring
  rw [he] at hd
  have hds : LocalWave s K P β (fun n i x =>
      Complex.ofReal (s.epsilon n * (a.frequency n i) ^ 2 * ‖a.normal s d n i x‖ ^ 2) * f n i x j)
        := by
    simpa only [smul_smul, Complex.real_smul, Complex.ofReal_mul, pow_two, mul_assoc] using hd
  simpa only [WaveFamily.principalVelocity, WaveFamily.coefficients,
    WaveCoefficients.principalVelocity,
    LinearWaveResidual.principal, Dfast, WaveFamily.normal, WaveCoefficients.normal, mul_zero,
      add_zero]
    using (hfast.add hK).add hds

theorem principalVelocity_class (h : InputBounds s K P α κ d a) {β : ℝ}
    {f : ℕ → I → D → ComplexVector}
    (hf : ∀ j, LocalWave s K P β (fun n i x => f n i x j)) :
    LocalWave s K P β (a.principalVelocity s d f) :=
  component_classes (h.principalVelocity_components hf)

theorem add_curl_amplitude (h : InputBounds s K P α κ d a) (hκ : κ ≤ 1 / 2)
    {f : ℕ → I → D → ComplexVector}
    (hf : ∀ j, LocalWave s K P (α + 1 / 2 - κ) (fun n i x => f n i x j)) :
    InputBounds s K P α κ d (a.addAmplitude f) :=
  { h with amplitude := fun j => (h.amplitude j).add ((hf j).mono_exponent (by linarith)) }

theorem with_cutoff (h : InputBounds s K P α κ d a) {ψ : ℕ → I → D → ℝ}
    (hψ : LocalUnweighted s K 0 ψ) : InputBounds s K P α κ d (a.withCutoff ψ) := by
  refine { h with amplitude := ?_, pressure := ?_ }
  · intro j
    simpa only [WaveFamily.withCutoff, Pi.smul_apply, zero_add] using
      unweighted_smul hψ (h.amplitude j)
  · simpa only [WaveFamily.withCutoff, zero_add] using real_mul_complex hψ h.pressure

theorem normalInverse_class (h : InputBounds s K P α κ d a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖a.normal s d n i x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖a.normal s d n i x‖ ≤ M) :
    LocalUnweighted s K 0 (fun n i x => (‖a.normal s d n i x‖ ^ 2)⁻¹) := by
  apply h.normal_norm_sq.inv (b := b ^ 2) (M := M ^ 2) (by positivity)
  · intro n i x hx hi
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ hb.le (norm_nonneg _)).mpr (hlower n i x hx hi)
  · intro n i x hx hi
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hupper n i x hx hi))).mpr
      (hupper n i x hx hi)

theorem normalCoefficient_class (h : InputBounds s K P α κ d a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖a.normal s d n i x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖a.normal s d n i x‖ ≤ M) :
    LocalWave s K P α (fun n i x =>
      CurlClassBounds.normalCoefficient (a.normal s d n i x) (a.amplitude n i x)) := by
  have hcross : LocalWave s K P α (fun n i x =>
      CurlClassBounds.normalCross (a.normal s d n i x) (a.amplitude n i x)) := by
    simpa only [one_mul, zero_add, CurlClassBounds.normalCross] using
      (h.normal.map CurlClassBounds.complexify).bilinear (component_classes h.amplitude)
        CurlClassBounds.complexCrossLinear
  simpa only [CurlClassBounds.normalCoefficient, zero_add] using
    unweighted_smul (h.normalInverse_class hb hlower hupper) hcross

/-- The inverse-normal factor and the cylindrical curl are estimated
from primitive local jets. Only support-local normal separation occurs. -/
theorem curlCorrection_class (h : InputBounds s K P α κ d a) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖a.normal s d n i x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖a.normal s d n i x‖ ≤ M)
    (hfreq : LocalUnweighted s K (1 / 2) (fun n i _ => 1 / a.frequency n i)) :
    LocalWave s K P (α + 1 / 2 - κ) (a.curlCorrection s d) := by
  let c : ℕ → I → D → ComplexVector := fun n i x =>
    CurlClassBounds.normalCoefficient (a.normal s d n i x) (a.amplitude n i x)
  have hc : LocalWave s K P α c := h.normalCoefficient_class hb hlower hupper
  have hDr (j : Fin 3) : LocalWave s K P (α - κ) (Dr d (fun n i x => c n i x j)) :=
    Dr_mem d (hc.map (ContinuousLinearMap.proj j)) h.radial_profile h.radial_scale h.loss_nonneg
  have hDz (j : Fin 3) : LocalWave s K P (α - κ) (Dz d s (fun n i x => c n i x j)) :=
    (Dz_mem d (hc.map (ContinuousLinearMap.proj j))).mono_exponent (by linarith [h.loss_nonneg])
  have hDθ (j : Fin 3) : LocalWave s K P (α - κ) (fun n i x =>
      (a.radius n i x)⁻¹ • along (fun _ => d.angular) (fun y => c n i y j) x) := by
    exact (unweighted_smul h.inverse_radius ((hc.map (ContinuousLinearMap.proj j)).directional
      d.angular)).mono_exponent
      (by linarith [h.loss_nonneg])
  have hconn (j : Fin 3) : LocalWave s K P (α - κ) (fun n i x => (a.radius n i x)⁻¹ • c n i x j) :=
    (unweighted_smul h.inverse_radius (hc.map (ContinuousLinearMap.proj j))).mono_exponent
      (by linarith [h.loss_nonneg])
  have hcurl : LocalWave s K P (α - κ) (fun n i =>
      CurlClassBounds.cylindricalCurl (a.radius n i) (d.radialField n) (fun _ => d.angular)
        (d.axialField s n) (c n i)) := by
    apply component_classes
    intro j
    fin_cases j
    · have hh := (hDθ 2).sub (hDz 1)
      simp only [CurlClassBounds.cylindricalCurl, Dz] at hh ⊢
      exact hh
    · have hh := (hDz 0).sub (hDr 2)
      simp only [CurlClassBounds.cylindricalCurl, Dz, Dr] at hh ⊢
      exact hh
    · have hh := ((hDr 1).add (hconn 1)).sub (hDθ 0)
      simp only [CurlClassBounds.cylindricalCurl, Dr] at hh ⊢
      exact hh
  have hi := hcurl.map (Complex.I • ContinuousLinearMap.id ℝ ComplexVector)
  have hfinal := unweighted_smul hfreq hi
  have he : (1 / 2 : ℝ) + (α - κ) = α + 1 / 2 - κ := by ring
  simp only [he, _root_.smul_apply, ContinuousLinearMap.id_apply, c, WaveFamily.coefficients,
    WaveFamily.normal, WaveCoefficients.normal]
    at hfinal ⊢
  exact hfinal

/-- The retained good coefficient is the literal principal operator of
the curl difference plus the literal remainder of the corrected field. -/
theorem retainedGood_class (h : InputBounds s K P α κ d a) (hκ : κ ≤ 1 / 2)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ K n i → b ≤ ‖a.normal s d n i x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ K n i → ‖a.normal s d n i x‖ ≤ M)
    (hfreq : LocalUnweighted s K (1 / 2) (fun n i _ => 1 / a.frequency n i)) :
    LocalWave s K P (α + 1 / 2 - 3 * κ) (a.retainedGood s d) := by
  have hc := h.curlCorrection_class hb hlower hupper hfreq
  have hci j := hc.map (ContinuousLinearMap.proj j)
  have hp := (h.principalVelocity_class hci).mono_exponent
    (show α + 1 / 2 - 3 * κ ≤ α + 1 / 2 - κ by linarith [h.loss_nonneg])
  exact hp.add (h.add_curl_amplitude hκ hci).remainder_class

/-- Primitive estimates may be restricted to a smaller native patch.
Only the derived, supported outputs are extended to the whole copy cell. -/
theorem classes_on_of_input_germs {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {C K : ℕ → I → Set D} {P : ℕ → I → D → ℝ}
    {α κ : ℝ} {d : GraphDirections D} {a : WaveFamily D I}
    (h : InputBounds s C P α κ d a) (hκ : κ ≤ 1 / 2)
    {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ C n i → b ≤ ‖a.normal s d n i x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ C n i → ‖a.normal s d n i x‖ ≤ M)
    (hfreq : LocalUnweighted s C (1 / 2) (fun n i _ => 1 / a.frequency n i))
    (hcover : ∀ n i x, x ∈ s.domain → x ∈ K n i → x ∈ C n i ∨
      (a.amplitude n i =ᶠ[𝓝 x] fun _ => 0) ∧ (a.pressure n i =ᶠ[𝓝 x] fun _ => 0)) :
    LocalWave s K P α a.amplitude ∧
    LocalWave s K P α (a.addAmplitude (a.curlCorrection s d)).amplitude ∧
    LocalWave s K P (α + 1 / 2) a.pressure ∧
    LocalWave s K P (α + 1 / 2 - κ) (a.curlCorrection s d) ∧
    LocalWave s K P (α + 1 / 2 - 3 * κ) (a.retainedGood s d) := by
  have hc := h.curlCorrection_class hb hlower hupper hfreq
  have hcor := h.add_curl_amplitude hκ (fun j => hc.map (ContinuousLinearMap.proj j))
  have hg := h.retainedGood_class hκ hb hlower hupper hfreq
  refine ⟨(component_classes h.amplitude).enlarge ?_,
    (component_classes hcor.amplitude).enlarge ?_, h.pressure.enlarge ?_,
    hc.enlarge ?_, hg.enlarge ?_⟩
  · intro n i x hx hi
    exact (hcover n i x hx hi).imp_right And.left
  · intro n i x hx hi
    exact (hcover n i x hx hi).imp_right
      (fun hz => (a.outputs_zero_germs s d hz.1 hz.2).2.1)
  · intro n i x hx hi
    exact (hcover n i x hx hi).imp_right And.right
  · intro n i x hx hi
    exact (hcover n i x hx hi).imp_right
      (fun hz => (a.outputs_zero_germs s d hz.1 hz.2).1)
  · intro n i x hx hi
    exact (hcover n i x hx hi).imp_right
      (fun hz => (a.outputs_zero_germs s d hz.1 hz.2).2.2)

end InputBounds

/-! ## Native copies and the whole lift -/

namespace LocalClass

theorem to_uniformLocalJets {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {L J : Type*} {s : StripData D}
    {K : L → ℕ → J → Set D} {w : L → ℕ → D → ℝ} {α : ℝ}
    {f : L → ℕ → J → D → E}
    (hf : LocalClass s (fun (n : ℕ) (i : L × J) => K i.1 n i.2)
      (fun n i x => w i.1 n x) α (fun n i => f i.1 n i.2)) :
    PeriodizedWaveBounds.UniformLocalJets s w α K f := by
  refine ⟨fun l n i x hx hi => hf.smooth n (l, i) x hx hi, fun m => ?_⟩
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun l n i x hx hi j hj => hb n (l, i) x hx hi j hj⟩

theorem of_uniformLocalJets {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {L J : Type*} {s : StripData D} {K : L → ℕ → J → Set D}
    {w : L → ℕ → D → ℝ} {α : ℝ} {f : L → ℕ → J → D → E}
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hf : PeriodizedWaveBounds.UniformLocalJets s w α K f) :
    LocalClass s (fun (n : ℕ) (i : L × J) => K i.1 n i.2)
      (fun n i x => w i.1 n x) α (fun n i => f i.1 n i.2) := by
  refine ⟨fun n i x hx => hw i.1 n x hx,
    fun n i x hx hi => hf.smooth i.1 n i.2 x hx hi, fun m => ?_⟩
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun n i x hx hi j hj => hb i.1 n i.2 x hx hi j hj⟩

end LocalClass

section CommonCopies

variable {D I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  (a : PeriodizedWaveBounds.CopyData D I)

noncomputable def nativeFamily : WaveFamily D I := WaveFamily.ofCoefficients a.localized

noncomputable def rawFamily : WaveFamily D I := WaveFamily.ofCoefficients a.raw

theorem common_curl_germ (K : PeriodizedWaveBounds.Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) {n : ℕ} {i : I} {x : D}
    (hx : x ∈ K.carrier n i) :
    a.common.curlCorrection s d n =ᶠ[𝓝 x] (a.localized i).curlCorrection s d n :=
  PeriodizedWaveBounds.curlCorrection_germ (a.common_amplitude_germ K hs n hx)
    (a.background.frequency n) (a.background.radius n) (a.background.phase n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)

theorem common_curl_zero_germ (K : PeriodizedWaveBounds.Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) {n : ℕ} {x : D}
    (hx : ∀ i, x ∉ K.carrier n i) :
    a.common.curlCorrection s d n =ᶠ[𝓝 x] fun _ => 0 := by
  have hh := PeriodizedWaveBounds.curlCorrection_germ (a.common_zero_germs K hs hx).1
    (a.background.frequency n) (a.background.radius n) (a.background.phase n)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
  simp only [PeriodizedWaveBounds.coefficient_zero, PeriodizedWaveBounds.curlRemainder_zero] at hh
  exact hh

/-- Primitive local input estimates imply all five actual common-field
classes. No global background normal, material defect, or remainder class
is a premise. The unused region is handled by genuine zero germs. -/
theorem common_bounds_from_native_local (K : PeriodizedWaveBounds.Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {s : StripData D} {d : GraphDirections D} {W : ℕ → D → ℝ} {α κ : ℝ}
    (hW : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (h : InputBounds s K.carrier (fun n _ => W n) α κ d (nativeFamily a))
    (hκ : κ ≤ 1 / 2) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i → b ≤ ‖a.background.normal s d n x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i → ‖a.background.normal s d n x‖ ≤ M)
    (hfreq : LocalUnweighted s K.carrier (1 / 2) (fun n _ _ => 1 / a.background.frequency n)) :
    WaveClass s W α a.common.amplitude ∧
    WaveClass s W α (a.commonCorrected s d).amplitude ∧
    WaveClass s W (α + 1 / 2) a.common.pressure ∧
    WaveClass s W (α + 1 / 2 - κ) (a.common.curlCorrection s d) ∧
    WaveClass s W (α + 1 / 2 - 3 * κ) (a.globalGood s d) := by
  have hw : ∀ n x, x ∈ s.domain → 0 ≤ Real.sqrt (s.zeta x) * W n x :=
    fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n x hx)
  have hc := h.curlCorrection_class hb hlower hupper hfreq
  have hci j := hc.map (ContinuousLinearMap.proj j)
  have hcorrected := h.add_curl_amplitude hκ hci
  have hgood := h.retainedGood_class hκ hb hlower hupper hfreq
  obtain ⟨ha, hp⟩ := a.common_classes K hs hw
    (component_classes h.amplitude).to_localJets h.pressure.to_localJets
  refine ⟨ha, ?_, hp, ?_, ?_⟩
  · exact a.commonCorrected_class_of_native K hs d hw
      (component_classes hcorrected.amplitude).to_localJets
  · apply PeriodizedWaveBounds.memClass_of_local_germs hw hc.to_localJets
    intro n x hx
    classical
    by_cases hi : ∃ i, x ∈ K.carrier n i
    · obtain ⟨i, hi⟩ := hi
      exact Or.inl ⟨i, hi, common_curl_germ a K hs s d hi⟩
    · exact Or.inr (common_curl_zero_germ a K hs s d (not_exists.mp hi))
  · exact a.globalGood_class_of_native K hs d hw hgood.to_localJets

theorem common_bounds_from_raw_local (K : PeriodizedWaveBounds.Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    {s : StripData D} {d : GraphDirections D} {W : ℕ → D → ℝ} {α κ : ℝ}
    (hW : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (h : InputBounds s K.carrier (fun n _ => W n) α κ d (rawFamily a))
    (hψ : LocalUnweighted s K.carrier 0 a.cutoff)
    (hκ : κ ≤ 1 / 2) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i → b ≤ ‖a.background.normal s d n x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i → ‖a.background.normal s d n x‖ ≤ M)
    (hfreq : LocalUnweighted s K.carrier (1 / 2) (fun n _ _ => 1 / a.background.frequency n)) :
    WaveClass s W α a.common.amplitude ∧
    WaveClass s W α (a.commonCorrected s d).amplitude ∧
    WaveClass s W (α + 1 / 2) a.common.pressure ∧
    WaveClass s W (α + 1 / 2 - κ) (a.common.curlCorrection s d) ∧
    WaveClass s W (α + 1 / 2 - 3 * κ) (a.globalGood s d) :=
  common_bounds_from_native_local a K hs hW (h.with_cutoff hψ) hκ hb hlower hupper hfreq

/-- The copy cell may be larger than the native phase patch. Primitive
jets are needed only on `C`; on the remaining points only the two input
zero germs are required. In particular no normal or defect estimate is
extended from `C` to `K.carrier`. -/
theorem common_bounds_from_supported_native (K : PeriodizedWaveBounds.Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i) (C : ℕ → I → Set D)
    {s : StripData D} {d : GraphDirections D} {W : ℕ → D → ℝ} {α κ : ℝ}
    (hW : ∀ n x, x ∈ s.domain → 0 ≤ W n x)
    (h : InputBounds s C (fun n _ => W n) α κ d (nativeFamily a))
    (hκ : κ ≤ 1 / 2) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ n i x, x ∈ s.domain → x ∈ C n i → b ≤ ‖a.background.normal s d n x‖)
    (hupper : ∀ n i x, x ∈ s.domain → x ∈ C n i → ‖a.background.normal s d n x‖ ≤ M)
    (hfreq : LocalUnweighted s C (1 / 2) (fun n _ _ => 1 / a.background.frequency n))
    (hcover : ∀ n i x, x ∈ s.domain → x ∈ K.carrier n i → x ∈ C n i ∨
      ((a.localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      ((a.localized i).pressure n =ᶠ[𝓝 x] fun _ => 0)) :
    WaveClass s W α a.common.amplitude ∧
    WaveClass s W α (a.commonCorrected s d).amplitude ∧
    WaveClass s W (α + 1 / 2) a.common.pressure ∧
    WaveClass s W (α + 1 / 2 - κ) (a.common.curlCorrection s d) ∧
    WaveClass s W (α + 1 / 2 - 3 * κ) (a.globalGood s d) := by
  have hw : ∀ n x, x ∈ s.domain → 0 ≤ Real.sqrt (s.zeta x) * W n x :=
    fun n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW n x hx)
  obtain ⟨ha, hcor, hp, hc, hg⟩ := h.classes_on_of_input_germs
    (K := K.carrier) hκ hb hlower hupper hfreq hcover
  obtain ⟨ha', hp'⟩ := a.common_classes K hs hw ha.to_localJets hp.to_localJets
  refine ⟨ha', a.commonCorrected_class_of_native K hs d hw hcor.to_localJets, hp', ?_,
    a.globalGood_class_of_native K hs d hw hg.to_localJets⟩
  apply PeriodizedWaveBounds.memClass_of_local_germs hw hc.to_localJets
  intro n x hx
  classical
  by_cases hi : ∃ i, x ∈ K.carrier n i
  · obtain ⟨i, hi⟩ := hi
    exact Or.inl ⟨i, hi, common_curl_germ a K hs s d hi⟩
  · exact Or.inr (common_curl_zero_germ a K hs s d (not_exists.mp hi))

theorem common_outputs_zero_germ (K : PeriodizedWaveBounds.Cells D I)
    (hs : ∀ n i, support (a.cutoff n i) ⊆ K.carrier n i)
    (s : StripData D) (d : GraphDirections D) {n : ℕ} {x : D}
    (hx : ∀ i, x ∉ K.carrier n i) :
    (a.common.amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 x] fun _ => 0) ∧
    ((a.commonCorrected s d).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.common.curlCorrection s d n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.globalGood s d n =ᶠ[𝓝 x] fun _ => 0) :=
  ⟨(a.common_zero_germs K hs hx).1, (a.common_zero_germs K hs hx).2,
    a.commonCorrected_zero_germ K hs s d hx, common_curl_zero_germ a K hs s d hx,
    a.globalGood_zero_germ K hs s d hx⟩

end CommonCopies

section UniformCopies

variable {D I : Type} {L : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  (a : L → PeriodizedWaveBounds.CopyData D I)

noncomputable def jointNativeFamily : WaveFamily D (L × I) :=
  WaveFamily.ofCoefficients (fun j => (a j.1).localized j.2)

/-- The same proof is uniform in an external spatial label. In particular,
no bound is chosen after fixing a label and then incorrectly made uniform. -/
theorem uniform_common_bounds_from_native_local (K : L → PeriodizedWaveBounds.Cells D I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    {s : StripData D} {d : GraphDirections D} {W : L → ℕ → D → ℝ} {α κ : ℝ}
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (h : InputBounds s (fun (n : ℕ) (j : L × I) => (K j.1).carrier n j.2)
      (fun n j x => W j.1 n x) α κ d (jointNativeFamily a))
    (hκ : κ ≤ 1 / 2) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i →
      b ≤ ‖(a l).background.normal s d n x‖)
    (hupper : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i →
      ‖(a l).background.normal s d n x‖ ≤ M)
    (hfreq : LocalUnweighted s (fun (n : ℕ) (j : L × I) => (K j.1).carrier n j.2)
      (1 / 2) (fun n j _ => 1 / (a j.1).background.frequency n)) :
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      α (fun l => (a l).common.amplitude) ∧
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      α (fun l => ((a l).commonCorrected s d).amplitude) ∧
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      (α + 1 / 2) (fun l => (a l).common.pressure) ∧
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      (α + 1 / 2 - κ) (fun l => (a l).common.curlCorrection s d) ∧
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      (α + 1 / 2 - 3 * κ) (fun l => (a l).globalGood s d) := by
  have hw : ∀ l n x, x ∈ s.domain → 0 ≤ Real.sqrt (s.zeta x) * W l n x :=
    fun l n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW l n x hx)
  have hc := h.curlCorrection_class hb (fun n j x hx hi => hlower j.1 n j.2 x hx hi)
    (fun n j x hx hi => hupper j.1 n j.2 x hx hi) hfreq
  have hci j := hc.map (ContinuousLinearMap.proj j)
  have hcorrected := h.add_curl_amplitude hκ hci
  have hg := h.retainedGood_class hκ hb (fun n j x hx hi => hlower j.1 n j.2 x hx hi)
    (fun n j x hx hi => hupper j.1 n j.2 x hx hi) hfreq
  have haj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) α (fun l => (K l).carrier)
      (fun l n i => ((a l).localized i).amplitude n) :=
    (component_classes h.amplitude).to_uniformLocalJets
  have hpj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) (α + 1 / 2) (fun l => (K l).carrier)
      (fun l n i => ((a l).localized i).pressure n) := h.pressure.to_uniformLocalJets
  have hcj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) (α + 1 / 2 - κ) (fun l => (K l).carrier)
      (fun l n i => ((a l).localized i).curlCorrection s d n) := hc.to_uniformLocalJets
  have hcorj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) α (fun l => (K l).carrier)
      (fun l n i => ((a l).corrected s d i).amplitude n) :=
    (component_classes hcorrected.amplitude).to_uniformLocalJets
  have hgj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) (α + 1 / 2 - 3 * κ) (fun l => (K l).carrier)
      (fun l n i => (a l).localGood s d n i) := hg.to_uniformLocalJets
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PeriodizedWaveBounds.copySum_uniformClass K hw
      (fun l => (a l).localized_amplitude_support (K l) (hs l)) haj
  · apply PeriodizedWaveBounds.uniformClass_of_local_germs hw hcorj
    intro l n x hx
    classical
    by_cases hi : ∃ i, x ∈ (K l).carrier n i
    · obtain ⟨i, hi⟩ := hi
      exact Or.inl ⟨i, hi, (a l).commonCorrected_amplitude_germ (K l) (hs l) s d n hi⟩
    · exact Or.inr ((a l).commonCorrected_zero_germ (K l) (hs l) s d (not_exists.mp hi))
  · exact PeriodizedWaveBounds.copySum_uniformClass K hw
      (fun l => (a l).localized_pressure_support (K l) (hs l)) hpj
  · apply PeriodizedWaveBounds.uniformClass_of_local_germs hw hcj
    intro l n x hx
    classical
    by_cases hi : ∃ i, x ∈ (K l).carrier n i
    · obtain ⟨i, hi⟩ := hi
      exact Or.inl ⟨i, hi, common_curl_germ (a l) (K l) (hs l) s d hi⟩
    · exact Or.inr (common_curl_zero_germ (a l) (K l) (hs l) s d (not_exists.mp hi))
  · exact PeriodizedWaveBounds.copySum_uniformClass K hw
      (fun l => (a l).localGood_support (K l) (hs l) s d) hgj

/-- Support-local primitive estimates, uniform over both labels and
copies, imply the global uniform classes. The phase patch `C` is allowed
to be strictly smaller than each closed copy cell. -/
theorem uniform_common_bounds_from_supported_native (K : L → PeriodizedWaveBounds.Cells D I)
    (hs : ∀ l n i, support ((a l).cutoff n i) ⊆ (K l).carrier n i)
    (C : L → ℕ → I → Set D)
    {s : StripData D} {d : GraphDirections D} {W : L → ℕ → D → ℝ} {α κ : ℝ}
    (hW : ∀ l n x, x ∈ s.domain → 0 ≤ W l n x)
    (h : InputBounds s (fun (n : ℕ) (j : L × I) => C j.1 n j.2)
      (fun n j x => W j.1 n x) α κ d (jointNativeFamily a))
    (hκ : κ ≤ 1 / 2) {b M : ℝ} (hb : 0 < b)
    (hlower : ∀ l n i x, x ∈ s.domain → x ∈ C l n i →
      b ≤ ‖(a l).background.normal s d n x‖)
    (hupper : ∀ l n i x, x ∈ s.domain → x ∈ C l n i →
      ‖(a l).background.normal s d n x‖ ≤ M)
    (hfreq : LocalUnweighted s (fun (n : ℕ) (j : L × I) => C j.1 n j.2)
      (1 / 2) (fun n j _ => 1 / (a j.1).background.frequency n))
    (hcover : ∀ l n i x, x ∈ s.domain → x ∈ (K l).carrier n i → x ∈ C l n i ∨
      (((a l).localized i).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
      (((a l).localized i).pressure n =ᶠ[𝓝 x] fun _ => 0)) :
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      α (fun l => (a l).common.amplitude) ∧
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      α (fun l => ((a l).commonCorrected s d).amplitude) ∧
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      (α + 1 / 2) (fun l => (a l).common.pressure) ∧
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      (α + 1 / 2 - κ) (fun l => (a l).common.curlCorrection s d) ∧
    LabelSumBounds.UniformClass s (fun l n x => Real.sqrt (s.zeta x) * W l n x)
      (α + 1 / 2 - 3 * κ) (fun l => (a l).globalGood s d) := by
  have hw : ∀ l n x, x ∈ s.domain → 0 ≤ Real.sqrt (s.zeta x) * W l n x :=
    fun l n x hx => mul_nonneg (Real.sqrt_nonneg _) (hW l n x hx)
  obtain ⟨ha, hcor, hp, hc, hg⟩ := h.classes_on_of_input_germs
    (K := fun (n : ℕ) (j : L × I) => (K j.1).carrier n j.2)
    hκ hb (fun n j x hx hi => hlower j.1 n j.2 x hx hi)
    (fun n j x hx hi => hupper j.1 n j.2 x hx hi) hfreq
    (fun n j x hx hi => hcover j.1 n j.2 x hx hi)
  have haj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) α (fun l => (K l).carrier)
      (fun l n i => ((a l).localized i).amplitude n) := ha.to_uniformLocalJets
  have hpj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) (α + 1 / 2) (fun l => (K l).carrier)
      (fun l n i => ((a l).localized i).pressure n) := hp.to_uniformLocalJets
  have hcj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) (α + 1 / 2 - κ) (fun l => (K l).carrier)
      (fun l n i => ((a l).localized i).curlCorrection s d n) := hc.to_uniformLocalJets
  have hcorj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) α (fun l => (K l).carrier)
      (fun l n i => ((a l).corrected s d i).amplitude n) := hcor.to_uniformLocalJets
  have hgj : PeriodizedWaveBounds.UniformLocalJets s
      (fun l n x => Real.sqrt (s.zeta x) * W l n x) (α + 1 / 2 - 3 * κ) (fun l => (K l).carrier)
      (fun l n i => (a l).localGood s d n i) := hg.to_uniformLocalJets
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact PeriodizedWaveBounds.copySum_uniformClass K hw
      (fun l => (a l).localized_amplitude_support (K l) (hs l)) haj
  · apply PeriodizedWaveBounds.uniformClass_of_local_germs hw hcorj
    intro l n x hx
    classical
    by_cases hi : ∃ i, x ∈ (K l).carrier n i
    · obtain ⟨i, hi⟩ := hi
      exact Or.inl ⟨i, hi, (a l).commonCorrected_amplitude_germ (K l) (hs l) s d n hi⟩
    · exact Or.inr ((a l).commonCorrected_zero_germ (K l) (hs l) s d (not_exists.mp hi))
  · exact PeriodizedWaveBounds.copySum_uniformClass K hw
      (fun l => (a l).localized_pressure_support (K l) (hs l)) hpj
  · apply PeriodizedWaveBounds.uniformClass_of_local_germs hw hcj
    intro l n x hx
    classical
    by_cases hi : ∃ i, x ∈ (K l).carrier n i
    · obtain ⟨i, hi⟩ := hi
      exact Or.inl ⟨i, hi, common_curl_germ (a l) (K l) (hs l) s d hi⟩
    · exact Or.inr (common_curl_zero_germ (a l) (K l) (hs l) s d (not_exists.mp hi))
  · exact PeriodizedWaveBounds.copySum_uniformClass K hw
      (fun l => (a l).localGood_support (K l) (hs l) s d) hgj

end UniformCopies

/-! ## Exact identities on an actual open native patch -/

section LocalIdentities

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- These are geometric and angular identities on one genuine native
open set. They impose no condition on the rest of the fast lift. -/
structure ExactOn (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (n : ℕ) (U : Set D) : Prop where
  isOpen : IsOpen U
  radial_profile : ContDiffOn ℝ ∞ d.radialProfile U
  phase : ContDiffOn ℝ ∞ (a.phase n) U
  amplitude : ∀ j, ContDiffOn ℝ ∞ (fun x => a.amplitude n x j) U
  radius : ∀ x ∈ U, DifferentiableAt ℝ (a.radius n) x
  radial_base : ∀ x ∈ U, DifferentiableAt ℝ (a.radialBase n) x
  frequency_base : ∀ x ∈ U, DifferentiableAt ℝ (a.frequencyBase n) x
  axial_base : ∀ x ∈ U, DifferentiableAt ℝ (a.axialBase n) x
  pressure : ∀ x ∈ U, DifferentiableAt ℝ (a.pressure n) x
  radius_nonzero : ∀ x ∈ U, a.radius n x ≠ 0
  radial_radius : ∀ x ∈ U, along (d.radialField n) (a.radius n) x = 1
  base_angular : ∀ x ∈ U, ∀ j,
    along (fun _ => d.angular) (fun y =>
      LinearWaveResidual.base (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n) y
        j) x = 0
  amplitude_angular : ∀ j, EqOn
    (along (fun _ => d.angular) (fun y => a.amplitude n y j)) (fun _ => 0) U
  phase_angular : ∃ p : ℝ, EqOn (along (fun _ => d.angular) (a.phase n)) (fun _ => p) U
  pressure_angular : ∀ x ∈ U, along (fun _ => d.angular) (a.pressure n) x = 0

theorem harmonicResidual_eq_on {a : WaveCoefficients D} {s : StripData D}
    {d : GraphDirections D} {n : ℕ} {U : Set D} (h : ExactOn a s d n U)
    {x : D} (hx : x ∈ U) :
    a.harmonicResidual s d n x = fun j =>
      (a.principal s d n x j + a.remainder s d n x j) * carrier (a.frequency n) (a.phase n) x := by
  obtain ⟨pθ, hpθ⟩ := h.phase_angular
  have hr : ContDiffOn ℝ ∞ (d.radialField n) U :=
    contDiffOn_const.add ((h.radial_profile.smul contDiffOn_const).const_smul (d.radialScale n))
  exact LinearWaveResidual.linearResidual_mode_split (s.epsilon n) (a.frequency n)
    (a.radius n) (a.radialBase n) (a.frequencyBase n) (a.axialBase n)
    (d.fastField n) (fun _ => d.slow) h.isOpen hr contDiffOn_const contDiffOn_const
    h.phase h.amplitude (h.radius x hx) (h.radial_base x hx) (h.frequency_base x hx)
    (h.axial_base x hx) (h.radius_nonzero x hx) (h.radial_radius x hx) (h.base_angular x hx)
    h.amplitude_angular hpθ (h.pressure x hx) (h.pressure_angular x hx) hx

theorem principal_add_at (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (f : ℕ → D → ComplexVector) (n : ℕ) (x : D)
    (ha : ∀ j, DifferentiableAt ℝ (fun y => a.amplitude n y j) x)
    (hf : ∀ j, DifferentiableAt ℝ (fun y => f n y j) x) :
    (a.addAmplitude f).principal s d n x =
      a.principal s d n x + a.principalVelocity s d f n x := by
  ext j
  change LinearWaveResidual.principal _ _ _ _ _ _ _ _ _ _ (fun y => a.amplitude n y + f n y) _ x j
    = _
  unfold LinearWaveResidual.principal
  rw [show along (d.fastField n) (fun y => (a.amplitude n y + f n y) j) x =
      along (d.fastField n) (fun y => a.amplitude n y j) x +
        along (d.fastField n) (fun y => f n y j) x from along_add _ (ha j) (hf j)]
  fin_cases j <;>
    simp [WaveCoefficients.principal, WaveCoefficients.principalVelocity,
      LinearWaveResidual.principal,
      WaveCoefficients.addAmplitude, LinearWaveResidual.shear, Pi.add_apply] <;> ring

theorem principal_cutoff_at (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (ψ : ℕ → D → ℝ) (source : ℕ → D → ComplexVector) (n : ℕ) (x : D)
    (ha : ∀ j, DifferentiableAt ℝ (fun y => a.amplitude n y j) x)
    (hψ : DifferentiableAt ℝ (ψ n) x) :
    (a.withCutoff ψ).principal s d n x + source n x =
      ψ n x • (a.principal s d n x + source n x) +
        LinearWaveBounds.excludedSlotError d ψ a.amplitude source n x := by
  have hψC : DifferentiableAt ℝ (fun y => (ψ n y : ℂ)) x :=
    (Complex.ofRealCLM.hasFDerivAt.comp x hψ.hasFDerivAt).differentiableAt
  have hD (j : Fin 3) :
      along (d.fastField n) (fun y => (a.withCutoff ψ).amplitude n y j) x =
        Complex.ofReal (d.Dfast ψ n x) * a.amplitude n x j +
          (ψ n x : ℂ) * along (d.fastField n) (fun y => a.amplitude n y j) x := by
    change along (d.fastField n) (fun y => (ψ n y : ℂ) * a.amplitude n y j) x = _
    rw [along_mul _ hψC (ha j), along_ofReal _ hψ]
    rfl
  ext j
  simp only [WaveCoefficients.principal, LinearWaveResidual.principal, Pi.add_apply]
  rw [hD j]
  fin_cases j <;>
    simp [WaveCoefficients.withCutoff, LinearWaveResidual.principal,
      LinearWaveResidual.shear, LinearWaveBounds.excludedSlotError,
      Pi.add_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_sub] <;> ring

theorem corrected_coefficient_eq_good_add_excluded_at
    (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (ψ : ℕ → D → ℝ) (f source : ℕ → D → ComplexVector) (n : ℕ) (x : D)
    (ha : ∀ j, DifferentiableAt ℝ (fun y => a.amplitude n y j) x)
    (hψ : DifferentiableAt ℝ (ψ n) x)
    (hf : ∀ j, DifferentiableAt ℝ (fun y => f n y j) x)
    (hsolve : a.principal s d n x = -source n x) :
    ((a.withCutoff ψ).addAmplitude f).principal s d n x +
        ((a.withCutoff ψ).addAmplitude f).remainder s d n x + source n x =
      a.goodCoefficient s d ψ f n x + LinearWaveBounds.excludedSlotError d ψ a.amplitude source n x
        := by
  have hp := principal_add_at (a.withCutoff ψ) s d f n x
    (fun j => hψ.smul (ha j)) hf
  have hc := principal_cutoff_at a s d ψ source n x ha hψ
  rw [hsolve, neg_add_cancel, smul_zero, zero_add] at hc
  have he : (a.withCutoff ψ).principalVelocity s d f n x = a.principalVelocity s d f n x := rfl
  rw [hp, he, WaveCoefficients.goodCoefficient, ← hc]
  abel

/-- The cutoff/curl identity needs only native smoothness and actual
equations on an open native patch. No global `InputBounds` occurs. -/
theorem harmonicResidual_eq_good_add_excluded_on
    (a : WaveCoefficients D) (s : StripData D) (d : GraphDirections D)
    (ψ : ℕ → D → ℝ) (f source : ℕ → D → ComplexVector) (n : ℕ) {U : Set D}
    (h : ExactOn ((a.withCutoff ψ).addAmplitude f) s d n U)
    {x : D} (hx : x ∈ U)
    (ha : ∀ j, DifferentiableAt ℝ (fun y => a.amplitude n y j) x)
    (hψ : DifferentiableAt ℝ (ψ n) x)
    (hf : ∀ j, DifferentiableAt ℝ (fun y => f n y j) x)
    (hsolve : a.principal s d n x = -source n x) :
    ((a.withCutoff ψ).addAmplitude f).harmonicResidual s d n x +
        (fun j => source n x j * carrier (a.frequency n) (a.phase n) x) =
      (fun j => (a.goodCoefficient s d ψ f n x j +
        LinearWaveBounds.excludedSlotError d ψ a.amplitude source n x j) *
          carrier (a.frequency n) (a.phase n) x) := by
  rw [harmonicResidual_eq_on h hx]
  have he := corrected_coefficient_eq_good_add_excluded_at a s d ψ f source n x ha hψ hf hsolve
  ext j
  have hej := congrFun he j
  simp only [Pi.add_apply] at hej ⊢
  change (_ + _) * carrier (a.frequency n) (a.phase n) x +
      source n x j * carrier (a.frequency n) (a.phase n) x = _
  rw [← add_mul, hej]

end LocalIdentities

end NavierStokes.LocalizedWaveBounds
