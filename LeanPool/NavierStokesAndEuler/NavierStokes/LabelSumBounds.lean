/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalWaveSum
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.PrimaryPulseBounds

@[expose] public section

/-!
# Uniform weighted bounds for actual label sums

The constants in `UniformClass` are chosen before the label.  The spatial
sum estimates use the actual closed label windows and the existing finite
coloring, rather than the total number of labels in an active finite set.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology BigOperators

namespace NavierStokes.LabelSumBounds

open WeightedClasses

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

variable {ι κ E F G : Type*} {D : Type}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The finite-jet constants and polynomial degrees are independent of
both band and label.  The majorant may retain a label-dependent envelope. -/
structure UniformClass (s : StripData D) (w : ι → ℕ → D → ℝ) (α : ℝ)
    (f : ι → ℕ → D → E) : Prop where
  weight_nonneg : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x
  smooth : ∀ l n, ContDiffOn ℝ ∞ (f l n) s.domain
  bounds : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
    ∀ l n x, x ∈ s.domain → ∀ j : ℕ, j ≤ m →
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤ majorant s (w l) α C p n x

noncomputable abbrev UniformMeanClass (s : StripData D) (α : ℝ)
    (f : ι → ℕ → D → E) : Prop :=
  UniformClass s (fun _ _ x => s.zeta x) α f

noncomputable abbrev UniformWaveClass (s : StripData D) (P : ι → ℕ → D → ℝ) (α : ℝ)
    (f : ι → ℕ → D → E) : Prop :=
  UniformClass s (fun l n x => Real.sqrt (s.zeta x) * P l n x) α f

namespace UniformClass

variable {s : StripData D} {w v : ι → ℕ → D → ℝ} {α β : ℝ}
variable {f g : ι → ℕ → D → E}

theorem each (hf : UniformClass s w α f) (l : ι) : MemClass s (w l) α (f l) := by
  refine ⟨hf.weight_nonneg l, hf.smooth l, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, hb l⟩

theorem reindex (hf : UniformClass s w α f) (a : κ → ι) :
    UniformClass s (fun l => w (a l)) α (fun l => f (a l)) := by
  refine ⟨fun l => hf.weight_nonneg (a l), fun l => hf.smooth (a l), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  exact ⟨C, hC, p, fun l => hb (a l)⟩

theorem zero (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x) :
    UniformClass s w α (fun _ _ _ => (0 : E)) := by
  refine ⟨hw, fun _ _ => contDiffOn_const, ?_⟩
  intro m
  refine ⟨0, le_rfl, 0, ?_⟩
  intro l n x hx j hj
  simp [majorant]

theorem congr (hf : UniformClass s w α f) (hfg : ∀ l n, EqOn (f l n) (g l n) s.domain) :
    UniformClass s w α g := by
  refine ⟨hf.weight_nonneg, fun l n => (hf.smooth l n).congr
    (fun x hx => (hfg l n hx).symm), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro l n x hx j hj
  have he : f l n =ᶠ[𝓝 x] g l n :=
    eventually_of_mem (s.isOpen_domain.mem_nhds hx) (hfg l n)
  rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq he j]
  exact hb l n x hx j hj

theorem mono_weight (hf : UniformClass s w α f)
    (hv : ∀ l n x, x ∈ s.domain → 0 ≤ v l n x)
    (hwv : ∀ l n x, x ∈ s.domain → w l n x ≤ v l n x) : UniformClass s v α f := by
  refine ⟨hv, hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro l n x hx j hj
  apply (hb l n x hx j hj).trans
  exact mul_le_mul_of_nonneg_left (hwv l n x hx)
    (mul_nonneg (mul_nonneg hC (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)
      (pow_nonneg (s.growth_nonneg n x) p))

theorem mono_exponent (hf : UniformClass s w α f) (hβα : β ≤ α) :
    UniformClass s w β f := by
  refine ⟨hf.weight_nonneg, hf.smooth, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨C, hC, p, ?_⟩
  intro l n x hx j hj
  apply (hb l n x hx j hj).trans
  apply mul_le_mul_of_nonneg_right _ (hf.weight_nonneg l n x hx)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (s.growth_nonneg n x) p)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (s.epsilon_pos n) (s.epsilon_le_one n) hβα) hC

theorem add (hf : UniformClass s w α f) (hg : UniformClass s w α g) :
    UniformClass s w α (fun l n x => f l n x + g l n x) := by
  refine ⟨hf.weight_nonneg, fun l n => (hf.smooth l n).add (hg.smooth l n), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hg.bounds m
  refine ⟨A + B, add_nonneg hA hB, p + q, ?_⟩
  intro l n x hx j hj
  rw [fun_iteratedFDeriv_add_apply ((hf.each l).contDiffAt n hx j) ((hg.each l).contDiffAt n hx j)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (f l n) x‖ + ‖iteratedFDeriv ℝ j (g l n) x‖ := norm_add_le _ _
    _ ≤ majorant s (w l) α A p n x + majorant s (w l) α B q n x :=
      add_le_add (ha l n x hx j hj) (hb l n x hx j hj)
    _ ≤ majorant s (w l) α A (p + q) n x + majorant s (w l) α B (p + q) n x :=
      add_le_add (majorant_mono_degree s (w l) α hA (Nat.le_add_right p q) n x
        (hf.weight_nonneg l n x hx))
        (majorant_mono_degree s (w l) α hB (Nat.le_add_left q p) n x (hf.weight_nonneg l n x hx))
    _ = _ := by unfold majorant; ring

theorem map (hf : UniformClass s w α f) (L : E →L[ℝ] F) :
    UniformClass s w α (fun l n x => L (f l n x)) := by
  refine ⟨hf.weight_nonneg, fun l n => (hf.smooth l n).continuousLinearMap_comp L, ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, p, ?_⟩
  intro l n x hx j hj
  change ‖iteratedFDeriv ℝ j (L ∘ f l n) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left ((hf.each l).contDiffAt n hx j) le_rfl]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (f l n) x‖ := L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L‖ * majorant s (w l) α C p n x := mul_le_mul_of_nonneg_left
      (hb l n x hx j hj) (norm_nonneg _)
    _ = _ := by unfold majorant; ring

theorem neg (hf : UniformClass s w α f) :
    UniformClass s w α (fun l n x => -f l n x) := by
  simpa only [_root_.neg_apply, ContinuousLinearMap.id_apply] using
    hf.map (-(ContinuousLinearMap.id ℝ E))

theorem sub (hf : UniformClass s w α f) (hg : UniformClass s w α g) :
    UniformClass s w α (fun l n x => f l n x - g l n x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem sum (F : Finset κ) (f : κ → ι → ℕ → D → E)
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hf : ∀ k ∈ F, UniformClass s w α (f k)) :
    UniformClass s w α (fun l n x => ∑ k ∈ F, f k l n x) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (zero hw : UniformClass s w α (fun _ _ _ => (0 :
    E)))
  | @insert a F ha ih =>
      simpa only [Finset.sum_insert ha] using
        (hf a (Finset.mem_insert_self _ _)).add
          (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

end UniformClass

/-- Pointwise finite-jet Leibniz estimate. The two bounds may be frozen
values of variable envelopes at this point. -/
theorem bilinear_jet_bound (L : E →L[ℝ] F →L[ℝ] G) {U : Set D} (hU : IsOpen U)
    {f : D → E} {g : D → F} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {x : D} (hx : x ∈ U) {m j : ℕ} (hj : j ≤ m) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i ≤ m, ‖iteratedFDeriv ℝ i f x‖ ≤ A)
    (hb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g x‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun y => L (f y) (g y)) x‖ ≤ ‖L‖ * 2 ^ m * A * B := by
  have h := JetBounds.norm_iteratedFDeriv_bilinear_le_on L hU hf hg hx (nat_le_infty j)
  have hs : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖) ≤ 2 ^ m * A * B := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (ha i (hij.trans hj)) (Nat.cast_nonneg _))
          (hb (j - i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = (2 : ℝ) ^ j * A * B := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have hc : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [hc]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hB
  exact (h.trans (mul_le_mul_of_nonneg_left hs (norm_nonneg L))).trans_eq (by ring)

namespace UniformClass

variable {s : StripData D} {w v : ι → ℕ → D → ℝ} {α β : ℝ}
variable {f : ι → ℕ → D → E} {g : ι → ℕ → D → F}

theorem bilinear (hf : UniformClass s w α f) (hg : UniformClass s v β g)
    (L : E →L[ℝ] F →L[ℝ] G) :
    UniformClass s (fun l n x => w l n x * v l n x) (α + β)
      (fun l n x => L (f l n x) (g l n x)) := by
  refine ⟨fun l n x hx => mul_nonneg (hf.weight_nonneg l n x hx) (hg.weight_nonneg l n x hx),
    fun l n => (L.contDiff.comp_contDiffOn (hf.smooth l n)).clm_apply (hg.smooth l n), ?_⟩
  intro m
  obtain ⟨A, hA, p, ha⟩ := hf.bounds m
  obtain ⟨B, hB, q, hb⟩ := hg.bounds m
  refine ⟨‖L‖ * 2 ^ m * A * B, by positivity, p + q, ?_⟩
  intro l n x hx j hj
  calc
    _ ≤ ‖L‖ * 2 ^ m * majorant s (w l) α A p n x * majorant s (v l) β B q n x :=
      bilinear_jet_bound L s.isOpen_domain (hf.smooth l n) (hg.smooth l n) hx hj
        (majorant_nonneg s (w l) α hA p n x (hf.weight_nonneg l n x hx))
        (majorant_nonneg s (v l) β hB q n x (hg.weight_nonneg l n x hx))
        (ha l n x hx) (hb l n x hx)
    _ = (‖L‖ * 2 ^ m) *
        (majorant s (w l) α A p n x * majorant s (v l) β B q n x) := by ring
    _ = _ := by rw [majorant_mul]; unfold majorant; ring

end UniformClass

theorem uniform_wave_bilinear_mean {s : StripData D} {P : ι → ℕ → D → ℝ} {α β : ℝ}
    {f : ι → ℕ → D → E} {g : ι → ℕ → D → F}
    (hf : UniformWaveClass s P α f) (hg : UniformWaveClass s P β g)
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1) (L : E →L[ℝ] F →L[ℝ] G) :
    UniformMeanClass s (α + β) (fun l n x => L (f l n x) (g l n x)) := by
  apply (hf.bilinear hg L).mono_weight (fun _ _ x hx => s.zeta_nonneg x hx)
  intro l n x hx
  have hs : Real.sqrt (s.zeta x) * Real.sqrt (s.zeta x) = s.zeta x := by
    rw [← pow_two, Real.sq_sqrt (s.zeta_nonneg x hx)]
  calc
    _ = (Real.sqrt (s.zeta x) * Real.sqrt (s.zeta x)) * (P l n x * P l n x) := by ring
    _ = s.zeta x * (P l n x * P l n x) := by rw [hs]
    _ ≤ s.zeta x * 1 := mul_le_mul_of_nonneg_left
      (by nlinarith [hP0 l n x hx, hP1 l n x hx]) (s.zeta_nonneg x hx)
    _ = _ := mul_one _

/-! ## Closed, enlarged label windows -/

abbrev WindowPoint := ℝ × SlotColoring.Position

/-- The first coordinate is the logarithmic dyadic coordinate.  The
window includes a two-level closed band and the actual two-mesh spatial
box used by `SlotColoring`. -/
noncomputable def closedWindow (d : ℝ) (l : SlotColoring.Label) : Set WindowPoint :=
  Icc ((l.1 : ℝ) - 2) ((l.1 : ℝ) + 2) ×ˢ SlotColoring.physicalBox d l

theorem physicalBox_closed (d : ℝ) (l : SlotColoring.Label) :
    IsClosed (SlotColoring.physicalBox d l) := by
  have he : SlotColoring.physicalBox d l = ⋂ j : Fin 3,
      {x : SlotColoring.Position | |x j - SlotColoring.width d j l.1 * (l.2.1 j : ℝ)| ≤
        2 * SlotColoring.width d j l.1} := by
    ext x
    simp only [SlotColoring.physicalBox, Set.mem_ofPred_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter fun j => isClosed_le
    (((continuous_apply j).sub continuous_const).abs) continuous_const

theorem closedWindow_closed (d : ℝ) (l : SlotColoring.Label) : IsClosed (closedWindow d l) :=
  isClosed_Icc.prod (physicalBox_closed d l)

theorem closedWindow_adjacency {d : ℝ} {l k : SlotColoring.Label} {x : WindowPoint}
    (hl : 1 ≤ l.1) (hk : 1 ≤ k.1) (hne : l ≠ k)
    (hxl : x ∈ closedWindow d l) (hxk : x ∈ closedWindow d k) : SlotColoring.Adj d l k := by
  have hlk : l.1 ≤ k.1 + 4 := by
    have h : (l.1 : ℝ) ≤ (k.1 : ℝ) + 4 := by linarith [hxl.1.1, hxk.1.2]
    exact_mod_cast h
  have hkl : k.1 ≤ l.1 + 4 := by
    have h : (k.1 : ℝ) ≤ (l.1 : ℝ) + 4 := by linarith [hxk.1.1, hxl.1.2]
    exact_mod_cast h
  exact ⟨hl, hk, hne, hlk, hkl, x.2, hxl.2, hxk.2⟩

/-- The already constructed coloring remains injective on these closed
enlargements. Endpoints do not require a separate exceptional case. -/
theorem closedWindow_color_injective (d : ℝ) (x : WindowPoint) :
    Set.InjOn SlotColoring.colorData {l | 1 ≤ l.1 ∧ x ∈ closedWindow d l} := by
  intro l hl k hk hcolor
  by_contra hne
  exact SlotColoring.colorData_proper d
    (closedWindow_adjacency hl.1 hk.1 hne hl.2 hk.2) hcolor

theorem closedWindow_card_le (d : ℝ) (x : WindowPoint) (F : Finset SlotColoring.Label)
    (hF : ∀ l ∈ F, 1 ≤ l.1 ∧ x ∈ closedWindow d l) : F.card ≤ 2250 := by
  classical
  have hi : Set.InjOn SlotColoring.colorData (F : Set SlotColoring.Label) :=
    (closedWindow_color_injective d x).mono hF
  have hc := Finset.card_le_card_of_injOn (t := Finset.univ) SlotColoring.colorData
    (fun _ _ => Finset.mem_univ _) hi
  simpa only [Finset.card_univ, SlotColoring.palette_card] using hc

/-- The genuine closed dyadic-mask and slow-mask supports lie inside the
enlargement; the inclusion also applies to every derivative support. -/
theorem labelRegion_subset_closedWindow {d : ℝ} {l : SlotColoring.Label} {x : WindowPoint}
    (hl : 1 ≤ l.1) (hx : x ∈ PhysicalWaveSum.labelRegion d l) (hq : 0 < x.1) :
    (SquaredPartition.logCoordinate x.1, x.2) ∈ closedWindow d l := by
  have ht := PhysicalWaveSum.logCoordinate_in_band hq
    (PhysicalWaveSum.labelRegion_band hx).1 (PhysicalWaveSum.labelRegion_band hx).2
  refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  exact SquaredPartition.physicalSlowMask_tsupport_subset_physicalBox d hl _ _ hx.2

theorem physicalMask_tsupport_closedWindow {d : ℝ} {l : SlotColoring.Label} {x : WindowPoint}
    (hl : 1 ≤ l.1) (hq : 0 < x.1) (hx : x ∈ tsupport (PhysicalWaveSum.physicalMask d l)) :
    (SquaredPartition.logCoordinate x.1, x.2) ∈ closedWindow d l :=
  labelRegion_subset_closedWindow hl (PhysicalWaveSum.physicalMask_tsupport_subset d l hx) hq

theorem physicalMask_jet_tsupport_closedWindow {d : ℝ} {l : SlotColoring.Label} {x : WindowPoint}
    (hl : 1 ≤ l.1) (hq : 0 < x.1) (m : ℕ)
    (hx : x ∈ tsupport (iteratedFDeriv ℝ m (PhysicalWaveSum.physicalMask d l))) :
    (SquaredPartition.logCoordinate x.1, x.2) ∈ closedWindow d l :=
  physicalMask_tsupport_closedWindow hl hq ((tsupport_iteratedFDeriv_subset m) hx)

theorem window_card_le {d : ℝ} {x : WindowPoint} (F : Finset ι)
    (label : ι → SlotColoring.Label) (hinj : Set.InjOn label (F : Set ι))
    (hF : ∀ l ∈ F, 1 ≤ (label l).1 ∧ x ∈ closedWindow d (label l)) : F.card ≤ 2250 := by
  classical
  rw [← Finset.card_image_of_injOn hinj]
  apply closedWindow_card_le d x
  intro l hl
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
  exact hF a ha

theorem jet_zero_off_window {U : Set D} (hU : IsOpen U) {x : D} (hx : x ∈ U)
    {d : ℝ} {label : SlotColoring.Label} {χ : D → WindowPoint} (hχ : ContinuousAt χ x)
    {f : D → E} (hs : ∀ y ∈ U, f y ≠ 0 → χ y ∈ closedWindow d label)
    (hout : χ x ∉ closedWindow d label) (m : ℕ) : iteratedFDeriv ℝ m f x = 0 := by
  apply PhysicalWaveSum.jet_zero_off_tsupport
  intro hsupport
  exact hout (PhysicalWaveSum.closed_property_on_tsupport hU hx hχ
    (closedWindow_closed d label) hs hsupport)

/-- A finite active family may have arbitrarily many labels in total.
Only its at-most-2250 locally supported derivatives contribute at `x`. -/
theorem finite_sum_jet_bound {U : Set D} (hU : IsOpen U) {x : D} (hx : x ∈ U)
    (F : Finset ι) (label : ι → SlotColoring.Label)
    (hinj : Set.InjOn label (F : Set ι)) (hlevel : ∀ l ∈ F, 1 ≤ (label l).1)
    (d : ℝ) (χ : D → WindowPoint) (hχ : ContinuousAt χ x)
    (f : ι → D → E) (m : ℕ) (hf : ∀ l ∈ F, ContDiffAt ℝ m (f l) x)
    (hs : ∀ l ∈ F, ∀ y ∈ U, f l y ≠ 0 → χ y ∈ closedWindow d (label l))
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ l ∈ F, χ x ∈ closedWindow d (label l) → ‖iteratedFDeriv ℝ m (f l) x‖ ≤ B) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ l ∈ F, f l y) x‖ ≤ 2250 * B := by
  classical
  let A := F.filter (fun l => χ x ∈ closedWindow d (label l))
  have hAF : A ⊆ F := Finset.filter_subset _ _
  have hcard : A.card ≤ 2250 := window_card_le A label (hinj.mono hAF)
    (fun l hl => ⟨hlevel l (hAF hl), (Finset.mem_filter.mp hl).2⟩)
  have he : (∑ l ∈ A, iteratedFDeriv ℝ m (f l) x) =
      ∑ l ∈ F, iteratedFDeriv ℝ m (f l) x := by
    apply Finset.sum_subset hAF
    intro l hl hn
    apply jet_zero_off_window hU hx hχ (hs l hl) _ m
    intro hmem
    exact hn (Finset.mem_filter.mpr ⟨hl, hmem⟩)
  rw [PhysicalWaveSum.iteratedFDeriv_finset_sum_at F hf, ← he]
  calc
    _ ≤ ∑ l ∈ A, ‖iteratedFDeriv ℝ m (f l) x‖ := norm_sum_le _ _
    _ ≤ ∑ _l ∈ A, B := Finset.sum_le_sum fun l hl =>
      hb l (hAF hl) (Finset.mem_filter.mp hl).2
    _ = (A.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2250 * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

/-- The actual band-dependent finite label sum retains its weighted
exponent and polynomial degree. The coefficient constant is multiplied
by the fixed overlap bound, not by the active set's total cardinality. -/
theorem window_sum_memClass {s : StripData D} {w : ℕ → D → ℝ} {α : ℝ}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (d : ℝ) (χ : ℕ → D → WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    {f : ι → ℕ → D → E} (hf : UniformClass s (fun _ => w) α f)
    (hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)
    (hs : ∀ n l, l ∈ labels n → ∀ x ∈ s.domain,
      f l n x ≠ 0 → χ n x ∈ closedWindow d (label n l)) :
    MemClass s w α (fun n x => ∑ l ∈ labels n, f l n x) := by
  refine ⟨hw, fun n => ContDiffOn.sum (fun l _ => hf.smooth l n), ?_⟩
  intro m
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  refine ⟨2250 * C, by positivity, p, ?_⟩
  intro n x hx j hj
  have hbound := finite_sum_jet_bound s.isOpen_domain hx (labels n) (label n)
    (hinj n) (hlevel n) d (χ n) ((hχ n).continuousAt (s.isOpen_domain.mem_nhds hx))
    (fun l => f l n) j (fun l _ => (hf.each l).contDiffAt n hx j)
    (fun l hl => hs n l hl) (majorant_nonneg s w α hC p n x (hw n x hx))
    (fun l _ _ => hb l n x hx j hj)
  exact hbound.trans_eq (by unfold majorant; ring)

/-! ## Uniform estimates for the actual angular covariance -/

open HarmonicFields CorrectionState

theorem uniform_realCoefficients {s : StripData D} {P : ι → ℕ → D → ℝ} {α : ℝ}
    (a : ι → ℕ → Coefficients D)
    (ha : ∀ j, UniformWaveClass s P α (fun l n x => a l n j x)) (j : ℤ) :
    UniformWaveClass s P α (fun l n x => HarmonicResidual.realCoefficients (a l n) j x) := by
  have h := ((ha j).add ((ha (-j)).map (Complex.conjCLE : ℂ →L[ℝ] ℂ))).map
    (ContinuousLinearMap.mul ℝ ℂ (2 : ℂ)⁻¹)
  simp only [HarmonicResidual.realCoefficients_apply,
    ContinuousLinearMap.mul_apply'] at h ⊢
  exact h

theorem uniform_angularProduct {s : StripData D} {P : ι → ℕ → D → ℝ} {α β : ℝ}
    (a b : ι → ℕ → Coefficients D) (F : Finset ℤ)
    (hF : ∀ l n, (a l n).support ⊆ F)
    (ha : ∀ j ∈ F, UniformWaveClass s P α (fun l n x => a l n j x))
    (hb : ∀ j ∈ F, UniformWaveClass s P β (fun l n x => b l n (-j) x))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (k : ι → ℕ → ℝ) (phase : ι → ℕ → D → ℝ) (kp : ι → ℕ → ℤ)
    (hkp : ∀ l n, kp l n ≠ 0) :
    UniformMeanClass s (α + β) (fun l n x => HarmonicFields.angularMean (fun θ =>
      field (a l n) (k l n) (phase l n) (kp l n) (x, θ) *
        field (b l n) (k l n) (phase l n) (kp l n) (x, θ))) := by
  have hsum : UniformMeanClass s (α + β) (fun l n x => ∑ j ∈ F, a l n j x * b l n (-j) x) :=
    UniformClass.sum F _ (fun _ _ x hx => s.zeta_nonneg x hx)
      (fun j hj => uniform_wave_bilinear_mean (ha j hj) (hb j hj) hP0 hP1
        (ContinuousLinearMap.mul ℝ ℂ))
  apply hsum.congr
  intro l n x _
  dsimp only
  rw [HarmonicFields.angularMean_product (a l n) (b l n) (k l n) (phase l n) (hkp l n) x]
  symm
  apply Finset.sum_subset (hF l n)
  intro j _ hj
  rw [Finsupp.notMem_support_iff.mp hj]
  simp

/-- Real projection includes the conjugate harmonics. Angular integration
is evaluated before taking slow derivatives, so no phase derivative or
carrier frequency is paid in this covariance estimate. -/
theorem uniform_realAngularProduct {s : StripData D} {P : ι → ℕ → D → ℝ} {α β : ℝ}
    (a b : ι → ℕ → Coefficients D) (N : ℕ)
    (hband : ∀ l n, BandLimited (a l n) N)
    (ha : ∀ j, UniformWaveClass s P α (fun l n x => a l n j x))
    (hb : ∀ j, UniformWaveClass s P β (fun l n x => b l n j x))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (k : ι → ℕ → ℝ) (phase : ι → ℕ → D → ℝ) (kp : ι → ℕ → ℤ)
    (hkp : ∀ l n, kp l n ≠ 0) :
    UniformMeanClass s (α + β) (fun l => angularAverage (fun n p =>
      (field (a l n) (k l n) (phase l n) (kp l n) p).re *
        (field (b l n) (k l n) (phase l n) (kp l n) p).re)) := by
  have hF : ∀ l n, (HarmonicResidual.realCoefficients (a l n)).support ⊆
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro l n j hj
    have ht := HarmonicResidual.band_realCoefficients (hband l n) j hj
    simp only [Finset.mem_Icc]
    omega
  have hc := uniform_angularProduct
    (fun l n => HarmonicResidual.realCoefficients (a l n))
    (fun l n => HarmonicResidual.realCoefficients (b l n))
    (Finset.Icc (-(N : ℤ)) (N : ℤ)) hF
    (fun j _ => uniform_realCoefficients a ha j)
    (fun j _ => uniform_realCoefficients b hb (-j)) hP0 hP1 k phase kp hkp
  apply (hc.map Complex.reCLM).congr
  intro l n x _
  exact (HarmonicCovariance.realAngularProduct_eq (a l n) (b l n)
    (k l n) (phase l n) (hkp l n) x).symm

theorem uniform_mixedBlockCovariance {s : StripData D} {P : ι → ℕ → D → ℝ} {α β : ℝ}
    (a b : ι → HarmonicBlock D) (N : ℕ) (hband : ∀ l, (a l).BandLimited N)
    (hfreq : ∀ l, (b l).frequency = (a l).frequency)
    (hphase : ∀ l, (b l).phase = (a l).phase)
    (hangular : ∀ l, (b l).angularFrequency = (a l).angularFrequency)
    (ha : ∀ i j, UniformWaveClass s P α (fun l n x => (a l).velocity n i j x))
    (hb : ∀ i j, UniformWaveClass s P β (fun l n x => (b l).velocity n i j x))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (a l).angularFrequency n ≠ 0) (i j : Fin 3) :
    UniformMeanClass s (α + β)
      (fun l => bilinearCovariance (a l).oscillation (b l).oscillation i j) := by
  have hc := uniform_realAngularProduct (fun l n => (a l).velocity n i)
    (fun l n => (b l).velocity n j) N (fun l n => (hband l).1 n i)
    (ha i) (hb j) hP0 hP1 (fun l => (a l).frequency) (fun l => (a l).phase)
    (fun l => (a l).angularFrequency) hkp
  apply hc.congr
  intro l n x _
  simp only [bilinearCovariance, HarmonicBlock.oscillation, hfreq, hphase, hangular]

theorem uniform_blockCovariance {s : StripData D} {P : ι → ℕ → D → ℝ} {α : ℝ}
    (a : ι → HarmonicBlock D) (N : ℕ) (hband : ∀ l, (a l).BandLimited N)
    (ha : ∀ i j, UniformWaveClass s P α (fun l n x => (a l).velocity n i j x))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (a l).angularFrequency n ≠ 0) (i j : Fin 3) :
    UniformMeanClass s (α + α)
      (fun l => bilinearCovariance (a l).oscillation (a l).oscillation i j) :=
  uniform_mixedBlockCovariance a a N hband (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    ha ha hP0 hP1 hkp i j

/-! ## Actual finite sums and support-induced covariance diagonality -/

noncomputable def fieldSum (labels : ℕ → Finset ι) (u : ι → Oscillation D) : Oscillation D :=
  fun n p i => ∑ l ∈ labels n, u l n p i

noncomputable def AngularContinuous (u : Oscillation D) : Prop :=
  ∀ n x i, Continuous (fun θ : ℝ => u n (x, θ) i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem block_angularContinuous (a : HarmonicBlock D) : AngularContinuous a.oscillation :=
  fun n x i => Complex.continuous_re.comp
    (HarmonicFields.field_angular_continuous (a.velocity n i) (a.frequency n) (a.phase n)
      (a.angularFrequency n) x)

/-- Actual support in a slow-label window and its padded native slot,
viewed through one common auxiliary coordinate. -/
noncomputable def SupportedOscillations {d h : ℝ} {vr vt : TorusInverse.Plane}
    (sys : PartitionedCovariance.SlotSystem d h vr vt)
    (label : ℕ → ι → SlotColoring.Label) (χ : ℕ → D → WindowPoint)
    (Y : ℕ → D → TorusInverse.Plane) (U : Set D) (u : ι → Oscillation D) : Prop :=
  ∀ l n x, x ∈ U → ∀ θ i, u l n (x, θ) i ≠ 0 →
    χ n x ∈ closedWindow d (label n l) ∧
      Y n x ∈ SlotGeometry.liftedSupport (SlotColoring.nativeIndex h (label n l).1)
        (PartitionedCovariance.slotSet h sys.radius vr vt (label n l))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem supported_cross_product_zero {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    {label : ℕ → ι → SlotColoring.Label} {χ : ℕ → D → WindowPoint}
    {Y : ℕ → D → TorusInverse.Plane} {U : Set D} {u v : ι → Oscillation D}
    (hu : SupportedOscillations sys label χ Y U u)
    (hv : SupportedOscillations sys label χ Y U v)
    {l k : ι} {n : ℕ} (hl : 1 ≤ (label n l).1) (hk : 1 ≤ (label n k).1)
    (hne : label n l ≠ label n k) {x : D} (hx : x ∈ U) (θ : ℝ) (i j : Fin 3) :
    u l n (x, θ) i * v k n (x, θ) j = 0 := by
  by_cases hlu : u l n (x, θ) i = 0
  · simp only [hlu, zero_mul]
  by_cases hkv : v k n (x, θ) j = 0
  · simp only [hkv, mul_zero]
  obtain ⟨hwL, hsL⟩ := hu l n x hx θ i hlu
  obtain ⟨hwK, hsK⟩ := hv k n x hx θ j hkv
  exact (Set.disjoint_left.mp (sys.disjoint _ _ (closedWindow_adjacency hl hk hne hwL hwK))
    hsL hsK).elim

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_fieldSum_eq (labels : ℕ → Finset ι) (u v : ι → Oscillation D)
    (hu : ∀ l, AngularContinuous (u l)) (hv : ∀ l, AngularContinuous (v l))
    {U : Set D}
    (hcross : ∀ n l, l ∈ labels n → ∀ k, k ∈ labels n → l ≠ k →
      ∀ x ∈ U, ∀ θ i j, u l n (x, θ) i * v k n (x, θ) j = 0)
    (n : ℕ) {x : D} (hx : x ∈ U) (i j : Fin 3) :
    bilinearCovariance (fieldSum labels u) (fieldSum labels v) i j n x =
      ∑ l ∈ labels n, bilinearCovariance (u l) (v l) i j n x := by
  change HarmonicResidual.realAngularMean (fun θ =>
    (∑ l ∈ labels n, u l n (x, θ) i) * (∑ l ∈ labels n, v l n (x, θ) j)) = _
  have he : (fun θ => (∑ l ∈ labels n, u l n (x, θ) i) *
      (∑ l ∈ labels n, v l n (x, θ) j)) =
      fun θ => ∑ l ∈ labels n, u l n (x, θ) i * v l n (x, θ) j := by
    funext θ
    exact PartitionedCovariance.sum_product_diagonal (labels n) _ _
      (fun l hl k hk hlk => hcross n l hl k hk hlk x hx θ i j)
  rw [he]
  exact HarmonicResidual.realAngularMean_sum (labels n) _
    (fun l _ => (hu l n x i).mul (hv l n x j))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem supported_covariance_fieldSum_eq {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → WindowPoint) (Y : ℕ → D → TorusInverse.Plane) {U : Set D}
    (u v : ι → Oscillation D)
    (hu : ∀ l, AngularContinuous (u l)) (hv : ∀ l, AngularContinuous (v l))
    (hsu : SupportedOscillations sys label χ Y U u)
    (hsv : SupportedOscillations sys label χ Y U v)
    (n : ℕ) {x : D} (hx : x ∈ U) (i j : Fin 3) :
    bilinearCovariance (fieldSum labels u) (fieldSum labels v) i j n x =
      ∑ l ∈ labels n, bilinearCovariance (u l) (v l) i j n x := by
  apply covariance_fieldSum_eq labels u v hu hv _ n hx i j
  intro n l hl k hk hne x hx θ i j
  exact supported_cross_product_zero hsu hsv (hlevel n l hl) (hlevel n k hk)
    (fun he => hne (hinj n hl hk he)) hx θ i j

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_window_support {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    {label : ℕ → ι → SlotColoring.Label} {χ : ℕ → D → WindowPoint}
    {Y : ℕ → D → TorusInverse.Plane} {U : Set D} {u v : ι → Oscillation D}
    (hsu : SupportedOscillations sys label χ Y U u)
    (l : ι) (n : ℕ) {x : D} (hx : x ∈ U) (i j : Fin 3)
    (hne : bilinearCovariance (u l) (v l) i j n x ≠ 0) :
    χ n x ∈ closedWindow d (label n l) := by
  by_contra hout
  have hz (θ : ℝ) : u l n (x, θ) i = 0 := by
    by_contra hn
    exact hout (hsu l n x hx θ i hn).1
  apply hne
  simp only [bilinearCovariance, angularAverage, hz, zero_mul, intervalIntegral.integral_zero,
    zero_div]

/-- Generic covariance adapter. The next theorem supplies the uniform
single-label estimates directly from harmonic coefficients. -/
theorem supported_covariance_sum_mem {s : StripData D} {α : ℝ}
    {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    (Y : ℕ → D → TorusInverse.Plane) (u v : ι → Oscillation D)
    (hu : ∀ l, AngularContinuous (u l)) (hv : ∀ l, AngularContinuous (v l))
    (hsu : SupportedOscillations sys label χ Y s.domain u)
    (hsv : SupportedOscillations sys label χ Y s.domain v)
    (hcov : ∀ i j, UniformMeanClass s α (fun l => bilinearCovariance (u l) (v l) i j))
    (i j : Fin 3) :
    MeanClass s α (bilinearCovariance (fieldSum labels u) (fieldSum labels v) i j) := by
  have hs := window_sum_memClass labels label hinj hlevel d χ hχ (hcov i j)
    (fun _ x hx => s.zeta_nonneg x hx)
    (fun n l _ x hx hn => covariance_window_support hsu l n hx i j hn)
  apply WaveInteractionBounds.class_congr hs
  intro n x hx
  exact (supported_covariance_fieldSum_eq labels label hinj hlevel χ Y u v hu hv hsu hsv
    n hx i j).symm

/-- Uniform coefficients and genuine native-slot support prove the class
of the actual covariance of the assembled finite active label sums.
Different labels may have different phases and carriers. -/
theorem harmonic_covariance_sum_mem {s : StripData D} {P : ι → ℕ → D → ℝ} {α β : ℝ}
    {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    (Y : ℕ → D → TorusInverse.Plane)
    (a b : ι → HarmonicBlock D) (N : ℕ) (hband : ∀ l, (a l).BandLimited N)
    (hfreq : ∀ l, (b l).frequency = (a l).frequency)
    (hphase : ∀ l, (b l).phase = (a l).phase)
    (hangular : ∀ l, (b l).angularFrequency = (a l).angularFrequency)
    (ha : ∀ i j, UniformWaveClass s P α (fun l n x => (a l).velocity n i j x))
    (hb : ∀ i j, UniformWaveClass s P β (fun l n x => (b l).velocity n i j x))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hsu : SupportedOscillations sys label χ Y s.domain (fun l => (a l).oscillation))
    (hsv : SupportedOscillations sys label χ Y s.domain (fun l => (b l).oscillation))
    (i j : Fin 3) :
    MeanClass s (α + β) (bilinearCovariance
      (fieldSum labels (fun l => (a l).oscillation))
      (fieldSum labels (fun l => (b l).oscillation)) i j) :=
  supported_covariance_sum_mem labels label hinj hlevel χ hχ Y
    (fun l => (a l).oscillation) (fun l => (b l).oscillation)
    (fun l => block_angularContinuous (a l)) (fun l => block_angularContinuous (b l)) hsu hsv
    (uniform_mixedBlockCovariance a b N hband hfreq hphase hangular ha hb hP0 hP1 hkp) i j

/-! ## Support adapters for the actual native wave construction -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem SupportedOscillations.add {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    {label : ℕ → ι → SlotColoring.Label} {χ : ℕ → D → WindowPoint}
    {Y : ℕ → D → TorusInverse.Plane} {U : Set D} {u v : ι → Oscillation D}
    (hu : SupportedOscillations sys label χ Y U u)
    (hv : SupportedOscillations sys label χ Y U v) :
    SupportedOscillations sys label χ Y U (fun l => u l + v l) := by
  intro l n x hx θ i hn
  by_cases hzero : u l n (x, θ) i = 0
  · apply hv l n x hx θ i
    simpa only [Pi.add_apply, hzero, zero_add] using hn
  · exact hu l n x hx θ i hzero

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem SupportedOscillations.sub {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    {label : ℕ → ι → SlotColoring.Label} {χ : ℕ → D → WindowPoint}
    {Y : ℕ → D → TorusInverse.Plane} {U : Set D} {u v : ι → Oscillation D}
    (hu : SupportedOscillations sys label χ Y U u)
    (hv : SupportedOscillations sys label χ Y U v) :
    SupportedOscillations sys label χ Y U (fun l => u l - v l) := by
  intro l n x hx θ i hn
  by_cases hzero : u l n (x, θ) i = 0
  · apply hv l n x hx θ i
    simpa only [Pi.sub_apply, hzero, zero_sub, neg_ne_zero] using hn
  · exact hu l n x hx θ i hzero

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- A native covered profile and a supported slow factor give the exact
support predicate used above. This also covers derivatives of the slow
mask, since their closed supports lie in the same window. -/
theorem covered_product_supported {d h : ℝ} {vr vt : TorusInverse.Plane}
    (sys : PartitionedCovariance.SlotSystem d h vr vt)
    (label : ℕ → ι → SlotColoring.Label) (χ : ℕ → D → WindowPoint)
    (Y : ℕ → D → TorusInverse.Plane) (U : Set D)
    (a : ι → ℕ → D → ℝ → Fin 3 → ℝ)
    (f : ι → ℕ → D → ℝ → Fin 3 → TorusInverse.Plane → ℝ)
    (ha : ∀ l n x, x ∈ U → ∀ θ i, a l n x θ i ≠ 0 → χ n x ∈ closedWindow d (label n l))
    (hf : ∀ l n x, x ∈ U → ∀ θ i, support (f l n x θ i) ⊆
      PartitionedCovariance.slotSet h sys.radius vr vt (label n l)) :
    SupportedOscillations sys label χ Y U (fun l n p i =>
      a l n p.1 p.2 i * PartitionedCovariance.covered
        (SlotColoring.nativeIndex h (label n l).1) (f l n p.1 p.2 i) (Y n p.1)) := by
  intro l n x hx θ i hn
  obtain ⟨ha0, hf0⟩ := mul_ne_zero_iff.mp hn
  exact ⟨ha l n x hx θ i ha0, PartitionedCovariance.covered_support (hf l n x hx θ i) _ hf0⟩

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- The actual physical mask automatically supplies the slow-window
condition for a covered native wave, with arbitrary phase and amplitude. -/
theorem native_wave_supported {d h : ℝ} {vr vt : TorusInverse.Plane}
    (sys : PartitionedCovariance.SlotSystem d h vr vt)
    (label : ℕ → ι → SlotColoring.Label) (hlevel : ∀ n l, 1 ≤ (label n l).1)
    (q : ℕ → D → ℝ) (position : ℕ → D → SlotColoring.Position)
    (Y : ℕ → D → TorusInverse.Plane) (U : Set D) (hq : ∀ n x, x ∈ U → 0 < q n x)
    (scale : ι → ℕ → D → Fin 3 → ℝ)
    (f : ι → ℕ → D → Fin 3 → TorusInverse.Plane → ℝ)
    (mode : ι → ℕ → ℤ) (phase : ι → ℕ → D → TorusInverse.Plane → ℝ)
    (hf : ∀ l n x, x ∈ U → ∀ i, support (f l n x i) ⊆
      PartitionedCovariance.slotSet h sys.radius vr vt (label n l)) :
    SupportedOscillations sys label
      (fun n x => (SquaredPartition.logCoordinate (q n x), position n x)) Y U
      (fun l n p i => PartitionedCovariance.wave
        (scale l n p.1 i * PartitionedCovariance.physicalMask d (label n l)
          (q n p.1) (position n p.1))
        (SlotColoring.nativeIndex h (label n l).1) (f l n p.1 i)
        (mode l n) (phase l n p.1) (Y n p.1) p.2) := by
  intro l n x hx θ i hn
  obtain ⟨hprod, _⟩ := mul_ne_zero_iff.mp hn
  obtain ⟨hamp, hprof⟩ := mul_ne_zero_iff.mp hprod
  have hmask := (mul_ne_zero_iff.mp hamp).2
  have hregion : (q n x, position n x) ∈ PhysicalWaveSum.labelRegion d (label n l) :=
    PhysicalWaveSum.physicalMask_support_subset d (label n l) hmask
  exact ⟨labelRegion_subset_closedWindow (hlevel n l) hregion (hq n x hx),
    PartitionedCovariance.covered_support (hf l n x hx i) _ hprof⟩

/-- The signed tail-label convention used by PrimaryFieldAssembly is
injective and has positive levels for every chosen start `N ≥ 1`. -/
theorem signedTailLabel_admissible {N : ℕ} (hN : 1 ≤ N) :
    Function.Injective (PartitionedCovariance.signedTailLabel N) ∧
      ∀ a, 1 ≤ (PartitionedCovariance.signedTailLabel N a).1 := by
  refine ⟨PartitionedCovariance.signedTailLabel_injective N, ?_⟩
  intro a
  change 1 ≤ a.1.1 + N
  omega

/-! ## The full signed covariance remainder, below CorrectionStep -/

abbrev Tensor (D : Type) := Fin 3 → Fin 3 → ScalarField D

noncomputable def symmetricCovariance (u v : Oscillation D) : Tensor D :=
  bilinearCovariance u v + bilinearCovariance v u

/-- Definitionally the same five terms used by CorrectionStep. -/
noncomputable def signedRemainder (primary old tangent curl : Oscillation D) : Tensor D :=
  (bilinearCovariance old (tangent + curl) + bilinearCovariance (tangent + curl) old +
    bilinearCovariance (tangent + curl) (tangent + curl)) - symmetricCovariance primary tangent

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem AngularContinuous.add {u v : Oscillation D} (hu : AngularContinuous u)
    (hv : AngularContinuous v) : AngularContinuous (u + v) :=
  fun n x i => (hu n x i).add (hv n x i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem AngularContinuous.sub {u v : Oscillation D} (hu : AngularContinuous u)
    (hv : AngularContinuous v) : AngularContinuous (u - v) :=
  fun n x i => (hu n x i).sub (hv n x i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_add_left {u v w : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) (hw : AngularContinuous w) :
    bilinearCovariance (u + v) w = bilinearCovariance u w + bilinearCovariance v w := by
  funext i j n x
  change HarmonicResidual.realAngularMean (fun θ => (u n (x, θ) i + v n (x, θ) i) * w n (x, θ) j) =
    _
  simp only [add_mul]
  exact HarmonicResidual.realAngularMean_add
    ((hu n x i).fun_mul (hw n x j)) ((hv n x i).fun_mul (hw n x j))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_add_right {u v w : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) (hw : AngularContinuous w) :
    bilinearCovariance u (v + w) = bilinearCovariance u v + bilinearCovariance u w := by
  funext i j n x
  change HarmonicResidual.realAngularMean (fun θ => u n (x, θ) i * (v n (x, θ) j + w n (x, θ) j)) =
    _
  simp only [mul_add]
  exact HarmonicResidual.realAngularMean_add
    ((hu n x i).fun_mul (hv n x j)) ((hu n x i).fun_mul (hw n x j))

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_sub_left {u v w : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) (hw : AngularContinuous w) :
    bilinearCovariance (u - v) w = bilinearCovariance u w - bilinearCovariance v w := by
  funext i j n x
  simp only [bilinearCovariance, angularAverage, Pi.sub_apply, sub_mul,
    intervalIntegral.integral_sub (((hu n x i).fun_mul (hw n x j)).intervalIntegrable _ _)
      (((hv n x i).fun_mul (hw n x j)).intervalIntegrable _ _), sub_div]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_sub_right {u v w : Oscillation D}
    (hu : AngularContinuous u) (hv : AngularContinuous v) (hw : AngularContinuous w) :
    bilinearCovariance u (v - w) = bilinearCovariance u v - bilinearCovariance u w := by
  funext i j n x
  simp only [bilinearCovariance, angularAverage, Pi.sub_apply, mul_sub,
    intervalIntegral.integral_sub (((hu n x i).fun_mul (hv n x j)).intervalIntegrable _ _)
      (((hu n x i).fun_mul (hw n x j)).intervalIntegrable _ _), sub_div]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem signedRemainder_exact (primary old tangent curl : Oscillation D)
    (hp : AngularContinuous primary) (ho : AngularContinuous old)
    (ht : AngularContinuous tangent) (hc : AngularContinuous curl) :
    signedRemainder primary old tangent curl =
      symmetricCovariance (old - primary) tangent + symmetricCovariance old curl +
        bilinearCovariance (tangent + curl) (tangent + curl) := by
  unfold signedRemainder symmetricCovariance
  rw [covariance_add_right ho ht hc, covariance_add_left ht hc ho,
    covariance_sub_left ho hp ht, covariance_sub_right ht ho hp]
  abel

structure SameCarrier (a b : HarmonicBlock D) : Prop where
  frequency : b.frequency = a.frequency
  phase : b.phase = a.phase
  angular : b.angularFrequency = a.angularFrequency

noncomputable def addBlock (a b : HarmonicBlock D) : HarmonicBlock D :=
  { a with velocity := fun n i => a.velocity n i + b.velocity n i
           pressure := fun n => a.pressure n + b.pressure n }

noncomputable def subBlock (a b : HarmonicBlock D) : HarmonicBlock D :=
  { a with velocity := fun n i => a.velocity n i - b.velocity n i
           pressure := fun n => a.pressure n - b.pressure n }

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem addBlock_oscillation (a b : HarmonicBlock D) (h : SameCarrier a b) :
    (addBlock a b).oscillation = a.oscillation + b.oscillation := by
  funext n x i
  simp only [addBlock, HarmonicBlock.oscillation, HarmonicFields.field,
    HarmonicFields.evaluate_add, Complex.add_re, Pi.add_apply, h.frequency, h.phase, h.angular]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem subBlock_oscillation (a b : HarmonicBlock D) (h : SameCarrier a b) :
    (subBlock a b).oscillation = a.oscillation - b.oscillation := by
  funext n x i
  simp only [subBlock, HarmonicBlock.oscillation, HarmonicFields.field,
    HarmonicFields.evaluate_eq_hom, map_sub,
    Complex.sub_re, Pi.sub_apply, h.frequency, h.phase, h.angular]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem addBlock_band {a b : HarmonicBlock D} {N : ℕ}
    (ha : a.BandLimited N) (hb : b.BandLimited N) : (addBlock a b).BandLimited N :=
  ⟨fun n i => (ha.1 n i).add (hb.1 n i),
    fun n => (ha.2 n).add (hb.2 n)⟩

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem subBlock_band {a b : HarmonicBlock D} {N : ℕ}
    (ha : a.BandLimited N) (hb : b.BandLimited N) : (subBlock a b).BandLimited N :=
  ⟨fun n i => HarmonicResidual.band_sub (ha.1 n i) (hb.1 n i),
    fun n => HarmonicResidual.band_sub (ha.2 n) (hb.2 n)⟩

theorem uniform_symmetricCovariance {s : StripData D} {P : ι → ℕ → D → ℝ} {α β : ℝ}
    (a b : ι → HarmonicBlock D) (N : ℕ) (hband : ∀ l, (a l).BandLimited N)
    (hcarrier : ∀ l, SameCarrier (a l) (b l))
    (ha : ∀ i j, UniformWaveClass s P α (fun l n x => (a l).velocity n i j x))
    (hb : ∀ i j, UniformWaveClass s P β (fun l n x => (b l).velocity n i j x))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (a l).angularFrequency n ≠ 0) (i j : Fin 3) :
    UniformMeanClass s (α + β) (fun l => symmetricCovariance (a l).oscillation (b l).oscillation i
      j) := by
  have hf := uniform_mixedBlockCovariance a b N hband
    (fun l => (hcarrier l).frequency) (fun l => (hcarrier l).phase) (fun l => (hcarrier l).angular)
    ha hb hP0 hP1 hkp
  have hr : UniformMeanClass s (α + β)
      (fun l => bilinearCovariance (b l).oscillation (a l).oscillation i j) := by
    apply (hf j i).congr
    intro l n x _
    rw [bilinearCovariance_comm]
  exact (hf i j).add hr

/-- Input coefficient bounds with one witness uniform in all spatial
labels. The improved old-minus-primary bound is explicitly retained. -/
structure SignedFamily (s : StripData D) (P : ι → ℕ → D → ℝ) (α δ β η : ℝ) where
  primary : ι → HarmonicBlock D
  old : ι → HarmonicBlock D
  tangent : ι → HarmonicBlock D
  curl : ι → HarmonicBlock D
  bandwidth : ℕ
  primary_band : ∀ l, (primary l).BandLimited bandwidth
  old_band : ∀ l, (old l).BandLimited bandwidth
  tangent_band : ∀ l, (tangent l).BandLimited bandwidth
  curl_band : ∀ l, (curl l).BandLimited bandwidth
  primary_carrier : ∀ l, SameCarrier (old l) (primary l)
  tangent_carrier : ∀ l, SameCarrier (old l) (tangent l)
  curl_carrier : ∀ l, SameCarrier (old l) (curl l)
  old_bounds : ∀ i j, UniformWaveClass s P α (fun l n x => (old l).velocity n i j x)
  difference_bounds : ∀ i j, UniformWaveClass s P δ
    (fun l n x => (old l).velocity n i j x - (primary l).velocity n i j x)
  tangent_bounds : ∀ i j, UniformWaveClass s P β (fun l n x => (tangent l).velocity n i j x)
  curl_bounds : ∀ i j, UniformWaveClass s P η (fun l n x => (curl l).velocity n i j x)
  envelope_nonneg : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x
  envelope_le_one : ∀ l n x, x ∈ s.domain → P l n x ≤ 1
  angular_ne_zero : ∀ l n, (old l).angularFrequency n ≠ 0

theorem SignedFamily.uniform_remainder {s : StripData D} {P : ι → ℕ → D → ℝ} {α δ β η γ : ℝ}
    (f : SignedFamily s P α δ β η) (hβη : β ≤ η)
    (hγd : γ ≤ δ + β) (hγc : γ ≤ α + η) (hγs : γ ≤ 2 * β) (i j : Fin 3) :
    UniformMeanClass s γ (fun l => signedRemainder (f.primary l).oscillation
      (f.old l).oscillation (f.tangent l).oscillation (f.curl l).oscillation i j) := by
  let diff := fun l => subBlock (f.old l) (f.primary l)
  let inc := fun l => addBlock (f.tangent l) (f.curl l)
  have hdt : ∀ l, SameCarrier (diff l) (f.tangent l) := fun l =>
    ⟨(f.tangent_carrier l).frequency, (f.tangent_carrier l).phase, (f.tangent_carrier l).angular⟩
  have htc : ∀ l, SameCarrier (f.tangent l) (f.curl l) := fun l =>
    ⟨(f.curl_carrier l).frequency.trans (f.tangent_carrier l).frequency.symm,
      (f.curl_carrier l).phase.trans (f.tangent_carrier l).phase.symm,
      (f.curl_carrier l).angular.trans (f.tangent_carrier l).angular.symm⟩
  have hd := uniform_symmetricCovariance diff f.tangent f.bandwidth
    (fun l => subBlock_band (f.old_band l) (f.primary_band l)) hdt
    f.difference_bounds f.tangent_bounds f.envelope_nonneg f.envelope_le_one f.angular_ne_zero i j
  have hc := uniform_symmetricCovariance f.old f.curl f.bandwidth f.old_band f.curl_carrier
    f.old_bounds f.curl_bounds f.envelope_nonneg f.envelope_le_one f.angular_ne_zero i j
  have hinc : ∀ i j, UniformWaveClass s P β (fun l n x => (inc l).velocity n i j x) := by
    intro i j
    exact (f.tangent_bounds i j).add ((f.curl_bounds i j).mono_exponent hβη)
  have hi := uniform_blockCovariance inc f.bandwidth
    (fun l => addBlock_band (f.tangent_band l) (f.curl_band l)) hinc
    f.envelope_nonneg f.envelope_le_one
    (fun l n => by
      change (f.tangent l).angularFrequency n ≠ 0
      rw [(f.tangent_carrier l).angular]
      exact f.angular_ne_zero l n) i j
  have hall := ((hd.mono_exponent hγd).add (hc.mono_exponent hγc)).add
    (hi.mono_exponent (by linarith : γ ≤ β + β))
  apply hall.congr
  intro l n x _
  have he := congrArg (fun T : Tensor D => T i j n x)
    (signedRemainder_exact (f.primary l).oscillation (f.old l).oscillation
      (f.tangent l).oscillation (f.curl l).oscillation
      (block_angularContinuous _) (block_angularContinuous _)
      (block_angularContinuous _) (block_angularContinuous _))
  simpa only [diff, inc, subBlock_oscillation _ _ (f.primary_carrier l),
    addBlock_oscillation _ _ (htc l), Pi.add_apply] using he.symm

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem fieldSum_add (labels : ℕ → Finset ι) (u v : ι → Oscillation D) :
    fieldSum labels (fun l => u l + v l) = fieldSum labels u + fieldSum labels v := by
  funext n x i
  simp only [fieldSum, Pi.add_apply, Finset.sum_add_distrib]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem fieldSum_angularContinuous (labels : ℕ → Finset ι) (u : ι → Oscillation D)
    (hu : ∀ l, AngularContinuous (u l)) : AngularContinuous (fieldSum labels u) :=
  fun n x i => continuous_finsetSum (labels n) (fun l _ => hu l n x i)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem supported_signedRemainder_fieldSum_eq {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → WindowPoint) (Y : ℕ → D → TorusInverse.Plane) {U : Set D}
    (p o t c : ι → Oscillation D)
    (hp : ∀ l, AngularContinuous (p l)) (ho : ∀ l, AngularContinuous (o l))
    (ht : ∀ l, AngularContinuous (t l)) (hc : ∀ l, AngularContinuous (c l))
    (hsp : SupportedOscillations sys label χ Y U p)
    (hso : SupportedOscillations sys label χ Y U o)
    (hst : SupportedOscillations sys label χ Y U t)
    (hsc : SupportedOscillations sys label χ Y U c)
    (n : ℕ) {x : D} (hx : x ∈ U) (i j : Fin 3) :
    signedRemainder (fieldSum labels p) (fieldSum labels o)
      (fieldSum labels t) (fieldSum labels c) i j n x =
        ∑ l ∈ labels n, signedRemainder (p l) (o l) (t l) (c l) i j n x := by
  have hi : ∀ l, AngularContinuous (t l + c l) := fun l => (ht l).add (hc l)
  have hsi := hst.add hsc
  have hoi := supported_covariance_fieldSum_eq labels label hinj hlevel χ Y o
    (fun l => t l + c l) ho hi hso hsi n hx i j
  have hio := supported_covariance_fieldSum_eq labels label hinj hlevel χ Y
    (fun l => t l + c l) o hi ho hsi hso n hx i j
  have hii := supported_covariance_fieldSum_eq labels label hinj hlevel χ Y
    (fun l => t l + c l) (fun l => t l + c l) hi hi hsi hsi n hx i j
  have hpt := supported_covariance_fieldSum_eq labels label hinj hlevel χ Y p t hp ht hsp hst n hx
    i j
  have htp := supported_covariance_fieldSum_eq labels label hinj hlevel χ Y t p ht hp hst hsp n hx
    i j
  simp only [fieldSum_add] at hoi hio hii
  simp only [signedRemainder, symmetricCovariance, Pi.sub_apply, Pi.add_apply,
    hoi, hio, hii, hpt, htp, Finset.sum_add_distrib, Finset.sum_sub_distrib]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem signedRemainder_window_support {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    {label : ℕ → ι → SlotColoring.Label} {χ : ℕ → D → WindowPoint}
    {Y : ℕ → D → TorusInverse.Plane} {U : Set D} {p o t c : ι → Oscillation D}
    (hp : SupportedOscillations sys label χ Y U p)
    (ho : SupportedOscillations sys label χ Y U o)
    (ht : SupportedOscillations sys label χ Y U t)
    (hc : SupportedOscillations sys label χ Y U c)
    (l : ι) (n : ℕ) {x : D} (hx : x ∈ U) (i j : Fin 3)
    (hne : signedRemainder (p l) (o l) (t l) (c l) i j n x ≠ 0) :
    χ n x ∈ closedWindow d (label n l) := by
  by_contra hout
  have hz (u : ι → Oscillation D) (hu : SupportedOscillations sys label χ Y U u)
      (θ : ℝ) (k : Fin 3) : u l n (x, θ) k = 0 := by
    by_contra hn
    exact hout (hu l n x hx θ k hn).1
  apply hne
  simp only [signedRemainder, symmetricCovariance, bilinearCovariance, angularAverage,
    Pi.add_apply, Pi.sub_apply, hz p hp, hz o ho, hz t ht, hz c hc, zero_add, zero_mul,
    intervalIntegral.integral_zero, zero_div, sub_self]

/-- The full signed remainder of the actual assembled fields satisfies
the fixed target exponent, uniformly over arbitrary finite active label
sets.  The local overlap bound is independent of stage and total size. -/
theorem SignedFamily.remainder_sum_mem {s : StripData D} {P : ι → ℕ → D → ℝ} {α δ β η γ : ℝ}
    (f : SignedFamily s P α δ β η) (hβη : β ≤ η)
    (hγd : γ ≤ δ + β) (hγc : γ ≤ α + η) (hγs : γ ≤ 2 * β)
    {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    (Y : ℕ → D → TorusInverse.Plane)
    (hp : SupportedOscillations sys label χ Y s.domain (fun l => (f.primary l).oscillation))
    (ho : SupportedOscillations sys label χ Y s.domain (fun l => (f.old l).oscillation))
    (ht : SupportedOscillations sys label χ Y s.domain (fun l => (f.tangent l).oscillation))
    (hc : SupportedOscillations sys label χ Y s.domain (fun l => (f.curl l).oscillation))
    (i j : Fin 3) :
    MeanClass s γ (signedRemainder
      (fieldSum labels (fun l => (f.primary l).oscillation))
      (fieldSum labels (fun l => (f.old l).oscillation))
      (fieldSum labels (fun l => (f.tangent l).oscillation))
      (fieldSum labels (fun l => (f.curl l).oscillation)) i j) := by
  have hsum := window_sum_memClass labels label hinj hlevel d χ hχ
    (f.uniform_remainder hβη hγd hγc hγs i j) (fun _ x hx => s.zeta_nonneg x hx)
    (fun n l _ x hx hn => signedRemainder_window_support hp ho ht hc l n hx i j hn)
  apply WaveInteractionBounds.class_congr hsum
  intro n x hx
  exact (supported_signedRemainder_fieldSum_eq labels label hinj hlevel χ Y
    (fun l => (f.primary l).oscillation) (fun l => (f.old l).oscillation)
    (fun l => (f.tangent l).oscillation) (fun l => (f.curl l).oscillation)
    (fun l => block_angularContinuous _) (fun l => block_angularContinuous _)
    (fun l => block_angularContinuous _) (fun l => block_angularContinuous _)
    hp ho ht hc n hx i j).symm

theorem uniform_coefficients_of_nonzero {s : StripData D} {P : ι → ℕ → D → ℝ} {α : ℝ}
    (a : ι → HarmonicBlock D)
    (ha : ∀ i j, j ≠ 0 → UniformWaveClass s P α (fun l n x => (a l).velocity n i j x))
    (hz : ∀ l n i, (a l).velocity n i 0 = 0)
    (hP : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x) :
    ∀ i j, UniformWaveClass s P α (fun l n x => (a l).velocity n i j x) := by
  intro i j
  by_cases hj : j = 0
  · subst j
    have hzero : UniformWaveClass s P α (fun _ _ _ => (0 : ℂ)) :=
      UniformClass.zero (fun l n x hx => mul_nonneg (Real.sqrt_nonneg _) (hP l n x hx))
    apply hzero.congr
    intro l n x _
    simp only [hz, Pi.zero_apply]
  · exact ha i j hj

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem covariance_increment_exact (u v : Oscillation D)
    (hu : AngularContinuous u) (hv : AngularContinuous v) :
    bilinearCovariance (u + v) (u + v) - bilinearCovariance u u =
      bilinearCovariance u v + bilinearCovariance v u + bilinearCovariance v v := by
  rw [covariance_add_left hu hv (hu.add hv), covariance_add_right hu hu hv,
    covariance_add_right hv hu hv]
  abel

/-- The actual exact-minus-principal covariance after adding a supported
curl correction. Taking `α=1/2` and `β=1-κ` gives `3/2-κ`, with no factor
depending on the total number of active labels. -/
theorem harmonic_covariance_increment_sum_mem
    {s : StripData D} {P : ι → ℕ → D → ℝ} {α β : ℝ} (hαβ : α ≤ β)
    {d h : ℝ} {vr vt : TorusInverse.Plane}
    {sys : PartitionedCovariance.SlotSystem d h vr vt}
    (labels : ℕ → Finset ι) (label : ℕ → ι → SlotColoring.Label)
    (hinj : ∀ n, Set.InjOn (label n) (labels n : Set ι))
    (hlevel : ∀ n l, l ∈ labels n → 1 ≤ (label n l).1)
    (χ : ℕ → D → WindowPoint) (hχ : ∀ n, ContinuousOn (χ n) s.domain)
    (Y : ℕ → D → TorusInverse.Plane)
    (a b : ι → HarmonicBlock D) (N : ℕ)
    (hNa : ∀ l, (a l).BandLimited N) (hNb : ∀ l, (b l).BandLimited N)
    (hcarrier : ∀ l, SameCarrier (a l) (b l))
    (ha : ∀ i j, UniformWaveClass s P α (fun l n x => (a l).velocity n i j x))
    (hb : ∀ i j, UniformWaveClass s P β (fun l n x => (b l).velocity n i j x))
    (hP0 : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hP1 : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hkp : ∀ l n, (a l).angularFrequency n ≠ 0)
    (hsu : SupportedOscillations sys label χ Y s.domain (fun l => (a l).oscillation))
    (hsv : SupportedOscillations sys label χ Y s.domain (fun l => (b l).oscillation))
    (i j : Fin 3) :
    MeanClass s (α + β) (fun n x =>
      bilinearCovariance
        (fieldSum labels (fun l => (a l).oscillation) + fieldSum labels (fun l => (b
          l).oscillation))
        (fieldSum labels (fun l => (a l).oscillation) + fieldSum labels (fun l => (b
          l).oscillation)) i j n x -
      bilinearCovariance (fieldSum labels (fun l => (a l).oscillation))
        (fieldSum labels (fun l => (a l).oscillation)) i j n x) := by
  let u := fieldSum labels (fun l => (a l).oscillation)
  let v := fieldSum labels (fun l => (b l).oscillation)
  have hab := harmonic_covariance_sum_mem labels label hinj hlevel χ hχ Y a b N hNa
    (fun l => (hcarrier l).frequency) (fun l => (hcarrier l).phase)
    (fun l => (hcarrier l).angular) ha hb hP0 hP1 hkp hsu hsv
  have hba : MeanClass s (α + β) (bilinearCovariance v u i j) := by
    simpa only [bilinearCovariance_comm] using hab j i
  have hbb := harmonic_covariance_sum_mem labels label hinj hlevel χ hχ Y b b N hNb
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hb hb hP0 hP1
    (fun l n => by rw [(hcarrier l).angular]; exact hkp l n) hsv hsv i j
  have hall := ((hab i j).add hba).add (hbb.mono_exponent (by linarith : α + β ≤ β + β))
  apply WaveInteractionBounds.class_congr hall
  intro n x _
  exact (congrArg (fun T : Tensor D => T i j n x)
    (covariance_increment_exact u v
      (fieldSum_angularContinuous labels _ (fun l => block_angularContinuous (a l)))
      (fieldSum_angularContinuous labels _ (fun l => block_angularContinuous (b l))))).symm

/-! ## Joint-index input estimates and native derivative supports -/

/-- Joint `(band,label)` envelope estimates yield the required quantifier
order directly. A uniform polynomial change of slow scale is allowed.
Neither constants nor polynomial degrees are chosen after the label. -/
theorem uniformClass_of_envelopeJets {s : StripData D}
    {V : PhaseJetBounds.Domain (ℕ × ι) D} {W : (ℕ × ι) → D → ℝ}
    {a : (ℕ × ι) → D → E} (ha : PrimaryPulseBounds.EnvelopeJets V W a)
    {w : ι → ℕ → D → ℝ} {α K : ℝ} {q : ℕ} (hK : 1 ≤ K)
    (hscale : ∀ n l, V.scale (n, l) ≤ K * s.slow n ^ q)
    (hdom : ∀ n l, s.domain ⊆ V.carrier (n, l))
    (hw : ∀ l n x, x ∈ s.domain → 0 ≤ w l n x)
    (hW : ∀ l n x, x ∈ s.domain → W (n, l) x ≤ s.epsilon n ^ α * w l n x) :
    UniformClass s w α (fun l n => a (n, l)) := by
  refine ⟨hw, fun l n => (ha.smooth (n, l)).mono (hdom n l), ?_⟩
  intro N
  obtain ⟨C, hC, m, hb⟩ := ha.bound N
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨C * K ^ m, by positivity, q * m, ?_⟩
  intro l n x hx j hj
  have hp : V.scale (n, l) ^ m ≤ K ^ m * s.growth n x ^ (q * m) := by
    calc
      _ ≤ (K * s.slow n ^ q) ^ m :=
        pow_le_pow_left₀ (zero_le_one.trans (V.one_le_scale _)) (hscale n l) m
      _ = K ^ m * s.slow n ^ (q * m) := by rw [mul_pow, ← pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (s.slow_le_growth n x) _) (by
          positivity)
  calc
    _ ≤ C * V.scale (n, l) ^ m * W (n, l) x := hb (n, l) x (hdom n l hx) j hj
    _ ≤ C * V.scale (n, l) ^ m * (s.epsilon n ^ α * w l n x) :=
      mul_le_mul_of_nonneg_left (hW l n x hx) (mul_nonneg hC0
        (pow_nonneg (zero_le_one.trans (V.one_le_scale _)) _))
    _ ≤ C * (K ^ m * s.growth n x ^ (q * m)) * (s.epsilon n ^ α * w l n x) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC0)
        (mul_nonneg (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le (hw l n x hx))
    _ = _ := by unfold majorant; ring

theorem uniformWaveClass_of_envelopeJets {s : StripData D}
    {V : PhaseJetBounds.Domain (ℕ × ι) D} {W : (ℕ × ι) → D → ℝ}
    {a : (ℕ × ι) → D → E} (ha : PrimaryPulseBounds.EnvelopeJets V W a)
    {P : ι → ℕ → D → ℝ} {α K : ℝ} {q : ℕ} (hK : 1 ≤ K)
    (hscale : ∀ n l, V.scale (n, l) ≤ K * s.slow n ^ q)
    (hdom : ∀ n l, s.domain ⊆ V.carrier (n, l))
    (hP : ∀ l n x, x ∈ s.domain → 0 ≤ P l n x)
    (hW : ∀ l n x, x ∈ s.domain →
      W (n, l) x ≤ s.epsilon n ^ α * (Real.sqrt (s.zeta x) * P l n x)) :
    UniformWaveClass s P α (fun l n => a (n, l)) :=
  uniformClass_of_envelopeJets ha hK hscale hdom
    (fun l n x hx => mul_nonneg (Real.sqrt_nonneg _) (hP l n x hx)) hW

theorem uniformClass_of_polynomialJets {s : StripData D}
    {V : PhaseJetBounds.Domain (ℕ × ι) D} {a : (ℕ × ι) → D → E}
    (ha : PhaseJetBounds.PolynomialJets V a) {K : ℝ} {q : ℕ} (hK : 1 ≤ K)
    (hscale : ∀ n l, V.scale (n, l) ≤ K * s.slow n ^ q)
    (hdom : ∀ n l, s.domain ⊆ V.carrier (n, l)) :
    UniformClass s (fun _ _ _ => 1) 0 (fun l n => a (n, l)) :=
  uniformClass_of_envelopeJets (PrimaryPulseBounds.EnvelopeJets.of_polynomial ha)
    hK hscale hdom (fun _ _ _ _ => zero_le_one) (by intro l n x hx; simp)

theorem slotSet_isCompact (h r : ℝ) (vr vt : TorusInverse.Plane) (l : SlotColoring.Label) :
    IsCompact (PartitionedCovariance.slotSet h r vr vt l) := by
  have he : PartitionedCovariance.slotSet h r vr vt l =
      (fun z : ℝ × ℝ => PartitionedCovariance.slotCenter h l + z.1 • vr + z.2 • vt) ''
        (Icc (-(2 * r)) (2 * r) ×ˢ Icc (-(2 * r)) (2 * r)) := by
    ext x
    constructor
    · rintro ⟨ξ, η, hξ, hη, he⟩
      exact ⟨(ξ, η), ⟨abs_le.mp hξ, abs_le.mp hη⟩, he.symm⟩
    · rintro ⟨⟨ξ, η⟩, ⟨hξ, hη⟩, he⟩
      exact ⟨ξ, η, abs_le.mpr hξ, abs_le.mpr hη, he.symm⟩
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image
    ((continuous_const.add (continuous_fst.smul continuous_const)).add
      (continuous_snd.smul continuous_const))

/-- Native derivatives stay inside the same closed padded slot, including
entry and exit. Periodizing such a derivative can therefore reuse
`PartitionedCovariance.covered_support` and the original slot separation. -/
theorem native_jet_tsupport_subset {h r : ℝ} {vr vt : TorusInverse.Plane}
    {l : SlotColoring.Label} {f : TorusInverse.Plane → E}
    (hf : support f ⊆ PartitionedCovariance.slotSet h r vr vt l) (m : ℕ) :
    tsupport (iteratedFDeriv ℝ m f) ⊆ PartitionedCovariance.slotSet h r vr vt l :=
  (tsupport_iteratedFDeriv_subset m).trans (closure_minimal hf (slotSet_isCompact h r vr vt
    l).isClosed)

end NavierStokes.LabelSumBounds
