/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSumBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedRadialPrimitive
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalSignedRequest
public import LeanPool.NavierStokesAndEuler.NavierStokes.SpatialCurl

@[expose] public section

/-!
# Uniform weighted coefficients and physical wave sums

The constants below are selected before the label and the band.  The first
step absorbs the actual two flat edges, including every inverse-edge power.
Global smoothness and support then extend the estimate across the boundary.
The final passage uses genuine common-coordinate compositions and the
physical carrier estimates of `PhysicalWaveSum`.
-/

noncomputable section

namespace NavierStokes.PhysicalClassBounds

open Set Function Filter WeightedClasses LabelSumBounds
open scoped Topology ContDiff BigOperators


private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

/-- Explicit fixed flat-edge geometry, pulled back through any radial
coordinate.  This is an equality of the weights, not a bound on them. -/
structure FlatGeometry (s : StripData D) (cL cR L : ℝ) (ρ : D → ℝ) : Prop where
  left_pos : 0 < cL
  right_pos : 0 < cR
  position : ∀ x ∈ s.domain, ρ x ∈ Ioo 0 L
  delta_eq : ∀ x ∈ s.domain, s.delta x = WeightedRadialPrimitive.delta L (ρ x)
  zeta_eq : ∀ x ∈ s.domain, s.zeta x = WeightedRadialPrimitive.zeta cL cR L (ρ x)

theorem edge_rpow {x : ℝ} (hx : 0 < x) (a c : ℝ) :
    FlatCutoff.edge a x ^ c = FlatCutoff.edge (c * a) x := by
  rw [FlatCutoff.edge_of_pos a hx, FlatCutoff.edge_of_pos (c * a) hx,
    ← Real.exp_mul]
  congr 1
  ring

theorem zeta_rpow {L x : ℝ} (hx : x ∈ Ioo 0 L) (cL cR c : ℝ) :
    WeightedRadialPrimitive.zeta cL cR L x ^ c = WeightedRadialPrimitive.zeta (c * cL) (c * cR) L x
      := by
  rw [WeightedRadialPrimitive.zeta, Real.mul_rpow (FlatCutoff.edge_nonneg _ _)
    (FlatCutoff.edge_nonneg _ _), edge_rpow hx.1,
    edge_rpow (sub_pos.mpr hx.2), WeightedRadialPrimitive.zeta]

/-- Exponential flatness absorbs any fixed inverse-edge power, uniformly
at both endpoints and for every positive fractional power of the weight. -/
theorem flat_edge_uniform {cL cR c : ℝ} (hcL : 0 < cL) (hcR : 0 < cR)
    (hc : 0 < c) (L : ℝ) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Ioo (0 : ℝ) L,
      (max 1 (WeightedRadialPrimitive.delta L x)⁻¹) ^ m * WeightedRadialPrimitive.zeta cL cR L x ^
        c ≤ K := by
  obtain ⟨K, hK, hb⟩ := WeightedRadialPrimitive.weight_uniform_bound (mul_pos hc hcL) (mul_pos hc
    hcR) L m
  refine ⟨K, hK, ?_⟩
  intro x hx
  have hd : 1 ≤ (WeightedRadialPrimitive.delta L x)⁻¹ :=
    (one_le_inv₀ (WeightedRadialPrimitive.delta_pos hx)).mpr (WeightedRadialPrimitive.delta_le_one
      L x)
  rw [max_eq_right hd, zeta_rpow hx]
  simpa only [WeightedRadialPrimitive.weight, div_eq_mul_inv, inv_pow, mul_comm] using hb x hx

theorem FlatGeometry.uniform {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ s.domain,
      (max 1 (s.delta x)⁻¹) ^ m * s.zeta x ^ c ≤ K := by
  obtain ⟨K, hK, hb⟩ := flat_edge_uniform hg.left_pos hg.right_pos hc L m
  refine ⟨K, hK, fun x hx => ?_⟩
  rw [hg.delta_eq x hx, hg.zeta_eq x hx]
  exact hb (ρ x) (hg.position x hx)

theorem logStrip_flatGeometry {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) :
    FlatGeometry (WeightedRadialPrimitive.logStripData (E := V) a b cL cR ha hcL hcR ε S hε hεone
      hS)
      cL cR (WeightedRadialPrimitive.logLength a b) (fun x => WeightedRadialPrimitive.logPosition a
        x.1) :=
  ⟨hcL, hcR, fun _ hx => WeightedRadialPrimitive.logPosition_mem ha hx, fun _ _ => rfl, fun _ _ =>
    rfl⟩

theorem movingStrip_flatGeometry {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    {a b cL cR : ℝ} (ha : 0 < a) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) :
    FlatGeometry (LocalSignedRequest.movingStripData U a b cL cR ha hcL hcR ε S hε hεone hS)
      cL cR (WeightedRadialPrimitive.logLength a b)
      (fun x => WeightedRadialPrimitive.logPosition a (LocalSignedRequest.profileMap coord x).1) :=
        by
  refine ⟨hcL, hcR, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  intro x hx
  exact WeightedRadialPrimitive.logPosition_mem ha
    ((LocalSignedRequest.movingStrip_domain U a b cL cR ha hcL hcR ε S hε hεone hS x).mp hx).2

/-- Remove the edge growth from an actual uniform coefficient class.  The
input envelope may depend on the label and band; its domination is uniform. -/
theorem UniformClass.edge_absorbed {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {c α : ℝ} (hc : 0 < c)
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (hf : UniformClass s w α f)
    (hw : ∀ l n x, x ∈ s.domain → w l n x ≤ s.zeta x ^ c) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n x, x ∈ s.domain → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤ A * s.epsilon n ^ α * s.slow n ^ p := by
  obtain ⟨C, hC, p, hb⟩ := hf.bounds m
  obtain ⟨K, hK, hKx⟩ := hg.uniform hc p
  refine ⟨C * K, mul_nonneg hC hK, p, ?_⟩
  intro l n x hx j hj
  have he : 0 ≤ s.epsilon n ^ α := (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le
  have hs : 0 ≤ s.slow n ^ p := pow_nonneg (zero_le_one.trans (s.one_le_slow n)) _
  calc
    _ ≤ majorant s (w l) α C p n x := hb l n x hx j hj
    _ ≤ C * s.epsilon n ^ α * s.growth n x ^ p * s.zeta x ^ c :=
      mul_le_mul_of_nonneg_left (hw l n x hx)
        (mul_nonneg (mul_nonneg hC he) (pow_nonneg (s.growth_nonneg n x) _))
    _ = (C * s.epsilon n ^ α * s.slow n ^ p) *
        ((max 1 (s.delta x)⁻¹) ^ p * s.zeta x ^ c) := by
      rw [StripData.growth, mul_pow]
      ring
    _ ≤ (C * s.epsilon n ^ α * s.slow n ^ p) * K :=
      mul_le_mul_of_nonneg_left (hKx x hx) (mul_nonneg (mul_nonneg hC he) hs)
    _ = _ := by ring

/-- The support boundary is included by continuity of the actual jets.
Outside it all jets vanish, because there is an actual zero neighborhood. -/
theorem jets_bound_global_of_support {f : D → E} {U : Set D} {B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hs : tsupport f ⊆ closure U)
    (m : ℕ) (hb : ∀ x ∈ U, ‖iteratedFDeriv ℝ m f x‖ ≤ B) :
    ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ B := by
  intro x
  by_cases hx : x ∈ closure U
  · exact (closure_minimal hb (isClosed_le
      (hf.continuous_iteratedFDeriv (nat_le_infty m)).norm continuous_const)) hx
  · rw [PhysicalWaveSum.jet_zero_off_tsupport f m (fun ht => hx (hs ht)), norm_zero]
    exact hB

omit [NormedSpace ℝ D] [NormedSpace ℝ E] in
theorem tsupport_subset_closure_of_zero {f : D → E} {U : Set D}
    (hf : ∀ x, x ∉ closure U → f x = 0) : tsupport f ⊆ closure U := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (hf x hn)

theorem UniformClass.edge_absorbed_global {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {c α : ℝ} (hc : 0 < c)
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (hf : UniformClass s w α f)
    (hw : ∀ l n x, x ∈ s.domain → w l n x ≤ s.zeta x ^ c)
    (hfc : ∀ l n, ContDiff ℝ ∞ (f l n))
    (hs : ∀ l n, tsupport (f l n) ⊆ closure s.domain) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n x, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤ A * s.epsilon n ^ α * s.slow n ^ p := by
  obtain ⟨A, hA, p, hb⟩ := UniformClass.edge_absorbed hg hc hf hw m
  refine ⟨A, hA, p, ?_⟩
  intro l n x j hj
  have hp : 0 ≤ A * s.epsilon n ^ α * s.slow n ^ p :=
    mul_nonneg (mul_nonneg hA (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)
      (pow_nonneg (zero_le_one.trans (s.one_le_slow n)) _)
  apply jets_bound_global_of_support (hfc l n) hp (hs l n) j
    (fun y hy => hb l n y hy j hj) x

/-- Conversion to physical band powers is exact; no exponent is lost when
the two flat edges are removed. -/
theorem UniformClass.chart_bound {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {c α h K : ℝ} {q : ℕ}
    (hc : 0 < c) (hK : 1 ≤ K)
    (hε : ∀ n, s.epsilon n = ChartScales.epsilon h n)
    (hslow : ∀ n, 4 ≤ n → s.slow n ≤ K * ChartScales.S n ^ q)
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (hf : UniformClass s w α f)
    (hw : ∀ l n x, x ∈ s.domain → w l n x ≤ s.zeta x ^ c)
    (hfc : ∀ l n, ContDiff ℝ ∞ (f l n))
    (hs : ∀ l n, tsupport (f l n) ⊆ closure s.domain) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n, 4 ≤ n → ∀ x, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤
        A * ChartScales.Q n ^ (h * α) * ChartScales.S n ^ p := by
  obtain ⟨A, hA, p, hb⟩ := UniformClass.edge_absorbed_global hg hc hf hw hfc hs m
  refine ⟨A * K ^ p, mul_nonneg hA (pow_nonneg (zero_le_one.trans hK) _), q * p, ?_⟩
  intro l n hn x j hj
  have he : s.epsilon n ^ α = ChartScales.Q n ^ (h * α) := by
    rw [hε, ChartScales.epsilon, ← Real.rpow_mul (ChartScales.Q_pos n).le]
  calc
    _ ≤ A * s.epsilon n ^ α * s.slow n ^ p := hb l n x j hj
    _ ≤ A * s.epsilon n ^ α * (K * ChartScales.S n ^ q) ^ p :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (zero_le_one.trans (s.one_le_slow n)) (hslow n hn) p)
        (mul_nonneg hA (Real.rpow_pos_of_pos (s.epsilon_pos n) α).le)
    _ = _ := by rw [he, mul_pow, ← pow_mul]; ring

theorem waveWeight_le {s : StripData D} {P : ι → ℕ → D → ℝ}
    (hP : ∀ l n x, x ∈ s.domain → P l n x ≤ 1) :
    ∀ l n x, x ∈ s.domain → Real.sqrt (s.zeta x) * P l n x ≤ s.zeta x ^ (1 / 2 : ℝ) := by
  intro l n x hx
  rw [← Real.sqrt_eq_rpow]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (hP l n x hx)

theorem UniformWaveClass.chart_bound {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {α h K : ℝ} {q : ℕ} (hK : 1 ≤ K)
    (hε : ∀ n, s.epsilon n = ChartScales.epsilon h n)
    (hslow : ∀ n, 4 ≤ n → s.slow n ≤ K * ChartScales.S n ^ q)
    {P : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (hf : UniformWaveClass s P α f)
    (hP : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hfc : ∀ l n, ContDiff ℝ ∞ (f l n))
    (hs : ∀ l n, tsupport (f l n) ⊆ closure s.domain) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n, 4 ≤ n → ∀ x, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤
        A * ChartScales.Q n ^ (h * α) * ChartScales.S n ^ p :=
  UniformClass.chart_bound hg (by norm_num : (0 : ℝ) < 1 / 2) hK hε hslow hf
    (waveWeight_le hP) hfc hs m

theorem UniformMeanClass.chart_bound {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {α h K : ℝ} {q : ℕ} (hK : 1 ≤ K)
    (hε : ∀ n, s.epsilon n = ChartScales.epsilon h n)
    (hslow : ∀ n, 4 ≤ n → s.slow n ≤ K * ChartScales.S n ^ q)
    {f : ι → ℕ → D → E} (hf : UniformMeanClass s α f)
    (hfc : ∀ l n, ContDiff ℝ ∞ (f l n))
    (hs : ∀ l n, tsupport (f l n) ⊆ closure s.domain) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n, 4 ≤ n → ∀ x, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤
        A * ChartScales.Q n ^ (h * α) * ChartScales.S n ^ p :=
  UniformClass.chart_bound hg (by norm_num : (0 : ℝ) < 1) hK hε hslow hf
    (by intro l n x hx; rw [Real.rpow_one]) hfc hs m

/-- Primitive input for the physical bridge.  In particular, `uniform`
places its constants before the label, and `support` concerns the actual
coefficient, not a prescribed bound for its derivatives. -/
structure SourceBounds (s : StripData D) (h α : ℝ)
    (w : ι → ℕ → D → ℝ) (f : ι → ℕ → D → E) : Prop where
  uniform : UniformClass s w α f
  flat_geometry : ∃ cL cR L : ℝ, ∃ ρ : D → ℝ, FlatGeometry s cL cR L ρ
  weight_le : ∃ c : ℝ, 0 < c ∧ ∀ l n x, x ∈ s.domain → w l n x ≤ s.zeta x ^ c
  epsilon_eq : ∀ n, s.epsilon n = ChartScales.epsilon h n
  slow_le : ∃ K : ℝ, 1 ≤ K ∧ ∃ q : ℕ,
    ∀ n, 4 ≤ n → s.slow n ≤ K * ChartScales.S n ^ q
  smooth : ∀ l n, ContDiff ℝ ∞ (f l n)
  support : ∀ l n, tsupport (f l n) ⊆ closure s.domain

theorem SourceBounds.chart_bound {s : StripData D} {h α : ℝ}
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (hf : SourceBounds s h α w f) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ l n, 4 ≤ n → ∀ x, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (f l n) x‖ ≤
        A * ChartScales.Q n ^ (h * α) * ChartScales.S n ^ p := by
  obtain ⟨cL, cR, L, ρ, hg⟩ := hf.flat_geometry
  obtain ⟨c, hc, hw⟩ := hf.weight_le
  obtain ⟨K, hK, q, hq⟩ := hf.slow_le
  exact UniformClass.chart_bound hg hc hK hf.epsilon_eq hq hf.uniform hw hf.smooth hf.support m

theorem SourceBounds.of_wave {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {h α K : ℝ} {q : ℕ} (hK : 1 ≤ K)
    (hε : ∀ n, s.epsilon n = ChartScales.epsilon h n)
    (hslow : ∀ n, 4 ≤ n → s.slow n ≤ K * ChartScales.S n ^ q)
    {P : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (hf : UniformWaveClass s P α f)
    (hP : ∀ l n x, x ∈ s.domain → P l n x ≤ 1)
    (hfc : ∀ l n, ContDiff ℝ ∞ (f l n))
    (hs : ∀ l n, tsupport (f l n) ⊆ closure s.domain) :
    SourceBounds s h α (fun l n x => Real.sqrt (s.zeta x) * P l n x) f :=
  ⟨hf, ⟨cL, cR, L, ρ, hg⟩, ⟨1 / 2, by norm_num, waveWeight_le hP⟩,
    hε, ⟨K, hK, q, hslow⟩, hfc, hs⟩

theorem SourceBounds.of_mean {s : StripData D} {cL cR L : ℝ} {ρ : D → ℝ}
    (hg : FlatGeometry s cL cR L ρ) {h α K : ℝ} {q : ℕ} (hK : 1 ≤ K)
    (hε : ∀ n, s.epsilon n = ChartScales.epsilon h n)
    (hslow : ∀ n, 4 ≤ n → s.slow n ≤ K * ChartScales.S n ^ q)
    {f : ι → ℕ → D → E} (hf : UniformMeanClass s α f)
    (hfc : ∀ l n, ContDiff ℝ ∞ (f l n))
    (hs : ∀ l n, tsupport (f l n) ⊆ closure s.domain) :
    SourceBounds s h α (fun _ _ x => s.zeta x) f :=
  ⟨hf, ⟨cL, cR, L, ρ, hg⟩, ⟨1, by norm_num, by intro l n x hx; rw [Real.rpow_one]⟩,
    hε, ⟨K, hK, q, hslow⟩, hfc, hs⟩

theorem SourceBounds.map {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : StripData D} {h α : ℝ} {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → E}
    (hf : SourceBounds s h α w f) (T : E →L[ℝ] V) :
    SourceBounds s h α w (fun l n x => T (f l n x)) := by
  refine ⟨hf.uniform.map T, hf.flat_geometry, hf.weight_le, hf.epsilon_eq, hf.slow_le,
    fun l n => T.contDiff.comp (hf.smooth l n), ?_⟩
  intro l n
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply hf.support l n
  apply subset_tsupport (f l n)
  intro he
  exact hx (by change T (f l n x) = 0; rw [he, map_zero])

section CommonCoordinates

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A local form of the genuine higher chain-rule estimate.  Only positive
derivatives of the coordinate map are needed; the map's values may be unbounded. -/
theorem composition_jet_bound {g : D → E} {φ : X → D} {U : Set X}
    (hg : ContDiff ℝ ∞ g) (hU : IsOpen U) (hφ : ContDiffOn ℝ ∞ φ U)
    {x : X} (hx : x ∈ U) (m : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hgb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i g (φ x)‖ ≤ A)
    (hφb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i φ x‖ ≤ B) :
    ∀ j ≤ m, ‖iteratedFDeriv ℝ j (g ∘ φ) x‖ ≤ (m.factorial : ℝ) * A * B ^ m := by
  intro j hj
  have hb := norm_iteratedFDerivWithin_comp_le hg.contDiffOn hφ (nat_le_infty j)
    uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ φ U) hx
    (C := A) (D := B)
    (fun i hi => by rw [iteratedFDerivWithin_univ]; exact hgb i (hi.trans hj))
    (fun i hi hij => by
      rw [iteratedFDerivWithin_of_isOpen i hU hx]
      exact (hφb i hi (hij.trans hj)).trans (by simpa using pow_le_pow_right₀ hB hi))
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at hb
  exact hb.trans (mul_le_mul
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hA)
    (pow_le_pow_right₀ hB hj) (by positivity) (by positivity))

/-- The common-chart identity for actual amplitudes.  This records only
the source formula and the coordinate map's jets, before any physical graph
or carrier has been differentiated. -/
structure CommonChart {H : ℕ} (F : PhysicalWaveSum.WaveFamily H)
    (a b h r0 σ : ℝ) (f : ι → ℕ → D → ℂ) where
  sourceIndex : PhysicalWaveSum.WaveIndex H → ι
  map : PhysicalWaveSum.WaveIndex H → PhysicalWaveSum.LiftPoint → D
  domain : PhysicalWaveSum.WaveIndex H → Set PhysicalWaveSum.LiftPoint
  open_domain : ∀ I, IsOpen (domain I)
  smooth : ∀ I, ContDiffOn ℝ ∞ (map I) (domain I)
  positive_jets : ∀ m : ℕ, ∃ B : ℝ, 1 ≤ B ∧ ∃ q : ℕ,
    ∀ I x, x ∈ domain I → ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j (map I) x‖ ≤ B * ChartScales.S I.1.val.1 ^ q
  amplitude_eq : ∀ I, F.amplitude I = fun x =>
    (ChartScales.Q I.1.val.1 ^ σ) • f (sourceIndex I) I.1.val.1 (map I x)
  contains : ∀ I z, z ∈ PhysicalWaveSum.preterminal →
    PhysicalWaveSum.physicalParams h z ∈
      PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    PhysicalWaveSum.commonLift h I.1.val.1 (F.gap I.1) z ∈ domain I

/-- Actual composition and the explicit band prefactor produce the
stripped amplitude estimate.  Its exponent is `h*α+σ`, and its constants
are independent of the label. -/
theorem CommonChart.amplitude_bound {s : StripData D} {h α σ a b r0 : ℝ}
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → ℂ}
    (hf : SourceBounds s h α w f) {H : ℕ} {F : PhysicalWaveSum.WaveFamily H}
    (hc : CommonChart F a b h r0 σ f) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ p : ℕ, ∀ I x, x ∈ hc.domain I → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (F.amplitude I) x‖ ≤
        A * ChartScales.Q I.1.val.1 ^ (h * α + σ) * ChartScales.S I.1.val.1 ^ p := by
  obtain ⟨A, hA, p, hb⟩ := hf.chart_bound m
  obtain ⟨B, hB, q, hq⟩ := hc.positive_jets m
  refine ⟨(m.factorial : ℝ) * A * B ^ m, by positivity, p + q * m, ?_⟩
  intro I x hx j hj
  have hS : 1 ≤ ChartScales.S I.1.val.1 := PhysicalGraphBounds.S_ge_one (by have := I.1.property;
    omega)
  have hQ := ChartScales.Q_pos I.1.val.1
  have hS0 : 0 ≤ ChartScales.S I.1.val.1 := zero_le_one.trans hS
  have hA0 : 0 ≤ A * ChartScales.Q I.1.val.1 ^ (h * α) * ChartScales.S I.1.val.1 ^ p := by
    positivity
  have hB0 : 1 ≤ B * ChartScales.S I.1.val.1 ^ q :=
    one_le_mul_of_one_le_of_one_le hB (one_le_pow₀ hS)
  have hjb := composition_jet_bound (hf.smooth (hc.sourceIndex I) I.1.val.1)
    (hc.open_domain I) (hc.smooth I) hx m hA0 hB0
    (fun k hk => hb (hc.sourceIndex I) I.1.val.1 I.1.property (hc.map I x) k hk)
    (fun k hk hkm => hq I x hx k hk hkm) j hj
  have hcomp : ContDiffAt ℝ ∞ (f (hc.sourceIndex I) I.1.val.1 ∘ hc.map I) x :=
    (hf.smooth (hc.sourceIndex I) I.1.val.1).contDiffAt.comp x
      ((hc.smooth I).contDiffAt ((hc.open_domain I).mem_nhds hx))
  rw [hc.amplitude_eq I]
  change ‖iteratedFDeriv ℝ j (fun x => (ChartScales.Q I.1.val.1 ^ σ) •
    (f (hc.sourceIndex I) I.1.val.1 ∘ hc.map I) x) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hcomp.of_le (nat_le_infty j)),
    norm_smul (ChartScales.Q I.1.val.1 ^ σ)
      (iteratedFDeriv ℝ j (f (hc.sourceIndex I) I.1.val.1 ∘ hc.map I) x),
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hQ σ).le]
  calc
    _ ≤ ChartScales.Q I.1.val.1 ^ σ * ((m.factorial : ℝ) *
        (A * ChartScales.Q I.1.val.1 ^ (h * α) * ChartScales.S I.1.val.1 ^ p) *
        (B * ChartScales.S I.1.val.1 ^ q) ^ m) :=
      mul_le_mul_of_nonneg_left hjb (Real.rpow_pos_of_pos hQ σ).le
    _ = _ := by rw [Real.rpow_add hQ, pow_add, mul_pow, ← pow_mul]; ring

end CommonCoordinates

/-- The natural slow scale for a band label is at least one because the
physical sum starts at band four. -/
noncomputable def bandDomain {V : Type} [NormedAddCommGroup V]
    (U : PhysicalWaveSum.BandLabel → Set V) (hU : ∀ L, IsOpen (U L)) :
    PhaseJetBounds.Domain PhysicalWaveSum.BandLabel V where
  scale L := ChartScales.S L.val.1
  carrier := U
  isOpen := hU
  one_le_scale L := PhysicalGraphBounds.S_ge_one (by have := L.property; omega)

/-- Polynomial jets of the actual two base profiles entering the phase,
on open slow-coordinate regions containing every relevant chart point. -/
structure CarrierBounds {H : ℕ} (F : PhysicalWaveSum.WaveFamily H) (a b h r0 : ℝ) where
  region : PhysicalWaveSum.BandLabel → Set PhysicalGraphBounds.Slow
  open_region : ∀ L, IsOpen (region L)
  jets : PhaseJetBounds.PolynomialJets (bandDomain region open_region)
    (fun L x => ((F.carrier L).F x, (F.carrier L).G x))
  contains : ∀ (I : PhysicalWaveSum.WaveIndex H) z,
    z ∈ PhysicalWaveSum.preterminal →
    PhysicalWaveSum.physicalParams h z ∈
      PhysicalWaveSum.labelRegion (CoordinateAlgebra.D h) I.1.val →
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PhysicalGraphBounds.annulus a b →
    ∀ chart : PolarCharts.Index,
    PhysicalGraphBounds.scaledRadial I.1.val.1 z ∈ PolarCharts.chartDomain a chart →
    (PhysicalGraphBounds.slotMap (PolarCharts.chart a chart)
      (ChartScales.timeCoefficient h I.1.val.1) (F.carrier I.1).center r0
      (PhysicalGraphBounds.physicalLift h I.1.val.1 z)).1 ∈ region I.1

theorem CarrierBounds.profile_bound {H : ℕ} {F : PhysicalWaveSum.WaveFamily H}
    {a b h r0 : ℝ} (hb : CarrierBounds F a b h r0) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ p : ℕ, ∀ L x, x ∈ hb.region L → ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (F.carrier L).F x‖ ≤ B * ChartScales.S L.val.1 ^ p ∧
      ‖iteratedFDeriv ℝ j (F.carrier L).G x‖ ≤ B * ChartScales.S L.val.1 ^ p := by
  obtain ⟨B, hB, p, hp⟩ := hb.jets.bound m
  refine ⟨B, hB, p, ?_⟩
  intro L x hx j hj
  have hpair := (hb.jets.smooth L).contDiffAt ((hb.open_region L).mem_nhds hx)
  have he := hp L j hj x hx
  rw [PhysicalGraphBounds.iteratedFDeriv_pair
    (hpair.fst.of_le (nat_le_infty j)) (hpair.snd.of_le (nat_le_infty j)),
    ContinuousMultilinearMap.opNorm_prod] at he
  exact ⟨(le_max_left _ _).trans he, (le_max_right _ _).trans he⟩

/-- The full `StrippedClass` is derived from the uniform weighted source,
the primitive common-chart identity, and the actual base-profile jets. -/
theorem strippedClass {s : StripData D} {h α σ a b r0 P : ℝ}
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → ℂ}
    (hf : SourceBounds s h α w f) {H : ℕ} {F : PhysicalWaveSum.WaveFamily H}
    (hc : CommonChart F a b h r0 σ f) (hb : CarrierBounds F a b h r0)
    (hp : ∀ L, |(F.carrier L).angular| ≤ P ∧
      |(F.carrier L).axial| ≤ P ∧ |(F.carrier L).radial| ≤ P) (m : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ B : ℝ, 1 ≤ B ∧ ∃ p q : ℕ,
      PhysicalWaveSum.StrippedClass F a b h r0 P A B (h * α + σ) p q m := by
  obtain ⟨A, hA, p, hAp⟩ := hc.amplitude_bound hf m
  obtain ⟨B, hB, q, hBq⟩ := hb.profile_bound m
  refine ⟨A, hA, B, hB, p, q, hp, ?_, ?_, ?_⟩
  · intro I z hz hregion hann j hj
    simpa only [Real.rpow_natCast] using
      hAp I _ (hc.contains I z hz hregion hann) j hj
  · intro I z hz hregion hann chart hchart j hj
    simpa only [Real.rpow_natCast] using
      (hBq I.1 _ (hb.contains I z hz hregion hann chart hchart) j hj).1
  · intro I z hz hregion hann chart hchart j hj
    simpa only [Real.rpow_natCast] using
      (hBq I.1 _ (hb.contains I z hz hregion hann chart hchart) j hj).2

/-- The derivative loss includes the displayed physical field rescaling.
It depends on the derivative order and fixed scaling parameters only. -/
noncomputable def physicalLoss (h σ : ℝ) (m : ℕ) : ℝ :=
  PhysicalGraphBounds.waveLoss h m - σ

/-- Full physical jets of the actual locally finite wave sum.  The
derivative-loss function does not depend on the harmonic cutoff, cover gap,
label, slow polynomial degrees, or correction stage. -/
theorem physical_sum_jet_bound {s : StripData D} {h α σ a b r0 Z P : ℝ}
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → ℂ}
    (hf : SourceBounds s h α w f) {H Δ : ℕ} {F : PhysicalWaveSum.WaveFamily H}
    (hc : CommonChart F a b h r0 σ f) (hb : CarrierBounds F a b h r0)
    (hr : PhysicalWaveSum.RegularFamily F a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ L, |(F.carrier L).angular| ≤ P ∧
      |(F.carrier L).axial| ≤ P ∧ |(F.carrier L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ProblemStatement.SpaceTime,
      z ∈ PhysicalWaveSum.preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (F.sum a h r0) z‖ ≤
        C * PhysicalWaveSum.physicalQ h z ^ (h * α - physicalLoss h σ m) := by
  obtain ⟨A, hA, B, hB, p, q, hclass⟩ := strippedClass hf hc hb hp m
  obtain ⟨C, hC, hbound⟩ := PhysicalWaveSum.physical_sum_jet_bound
    (b := b) hh hh1 ha hZ hr0 hP hB (Nat.cast_nonneg q) H Δ m
      (h * α + σ) p A hA
  refine ⟨C, hC, ?_⟩
  intro z hz ht
  convert! hbound F hr hclass z hz ht using 1
  congr 2
  unfold physicalLoss
  ring

theorem physical_vector_sum_jet_bound {s : StripData D} {h α σ a b r0 Z P : ℝ}
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → ℂ}
    (hf : SourceBounds s h α w f) {H Δ : ℕ} {F : Fin 3 → PhysicalWaveSum.WaveFamily H}
    (hc : ∀ i, CommonChart (F i) a b h r0 σ f)
    (hb : ∀ i, CarrierBounds (F i) a b h r0)
    (hr : ∀ i, PhysicalWaveSum.RegularFamily (F i) a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ i L, |((F i).carrier L).angular| ≤ P ∧
      |((F i).carrier L).axial| ≤ P ∧ |((F i).carrier L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ProblemStatement.SpaceTime,
      z ∈ PhysicalWaveSum.preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (PhysicalWaveSum.vectorSum F a h r0) z‖ ≤
        C * PhysicalWaveSum.physicalQ h z ^ (h * α - physicalLoss h σ m) := by
  classical
  have hs := fun i => physical_sum_jet_bound hf (hc i) (hb i) (hr i)
    hh hh1 ha hZ hr0 hP (hp i) m
  choose C hC hbound using hs
  refine ⟨3 * ∑ i : Fin 3, C i,
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => hC i)), ?_⟩
  intro z hz ht
  have hq := PhysicalWaveSum.physicalQ_pos hh hh1 hz
  have hi (i : Fin 3) : C i ≤ ∑ j : Fin 3, C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  have he := PhysicalWaveSum.vectorSum_jet_bound hr ha hh hh1 hz m
    (B := (∑ i : Fin 3, C i) * PhysicalWaveSum.physicalQ h z ^ (h * α - physicalLoss h σ m))
    (fun i => (hbound i z hz ht).trans
      (mul_le_mul_of_nonneg_right (hi i) (Real.rpow_pos_of_pos hq _).le))
  exact he.trans_eq (by ring)

/-- Taking the real part, as for the physical pressure, loses no constant. -/
theorem physical_real_sum_jet_bound {s : StripData D} {h α σ a b r0 Z P : ℝ}
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → ℂ}
    (hf : SourceBounds s h α w f) {H Δ : ℕ} {F : PhysicalWaveSum.WaveFamily H}
    (hc : CommonChart F a b h r0 σ f) (hb : CarrierBounds F a b h r0)
    (hr : PhysicalWaveSum.RegularFamily F a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ L, |(F.carrier L).angular| ≤ P ∧
      |(F.carrier L).axial| ≤ P ∧ |(F.carrier L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ProblemStatement.SpaceTime,
      z ∈ PhysicalWaveSum.preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (fun z => (F.sum a h r0 z).re) z‖ ≤
        C * PhysicalWaveSum.physicalQ h z ^ (h * α - physicalLoss h σ m) := by
  obtain ⟨C, hC, hbound⟩ := physical_sum_jet_bound hf hc hb hr hh hh1 ha hZ hr0 hP hp m
  refine ⟨C, hC, ?_⟩
  intro z hz ht
  have hsm := ((hr.sum_smooth ha hh hh1).contDiffAt
    (PhysicalWaveSum.preterminal_open.mem_nhds hz)).of_le (nat_le_infty m)
  have he := PhysicalWaveSum.norm_jet_linear_comp_at hsm Complex.reCLM
  have hn : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro c
    simpa only [Complex.reCLM_apply, one_mul, Real.norm_eq_abs] using Complex.abs_re_le_norm c
  exact he.trans ((mul_le_of_le_one_left (norm_nonneg _) hn).trans (hbound z hz ht))

/-- Inclusion of a spatial direction into a joint spacetime direction. -/
noncomputable def spatialInclusion : ProblemStatement.Space →L[ℝ] ProblemStatement.SpaceTime :=
  (0 : ProblemStatement.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ProblemStatement.Space)

/-- A fixed continuous linear map takes the spatial curl from a joint
Jacobian.  Its norm is independent of every band and correction stage. -/
noncomputable def jointCurl : (ProblemStatement.SpaceTime →L[ℝ] ProblemStatement.Space) →L[ℝ]
    ProblemStatement.Space :=
  SpatialCurl.curlLinear.comp
    ((ContinuousLinearMap.compL ℝ ProblemStatement.Space ProblemStatement.SpaceTime
      ProblemStatement.Space).flip spatialInclusion)

theorem spatialCurl_eq_joint {A : ProblemStatement.VelocityField} {z : ProblemStatement.SpaceTime}
    (hA : DifferentiableAt ℝ A z) :
    SpatialCurl.spatialCurl A z = jointCurl (fderiv ℝ A z) := by
  have hi : HasFDerivAt (fun y : ProblemStatement.Space => (z.1, y)) spatialInclusion z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hd := (hA.hasFDerivAt.comp z.2 hi).fderiv
  change SpatialCurl.curlLinear (fderiv ℝ (fun y => A (z.1, y)) z.2) =
    SpatialCurl.curlLinear ((fderiv ℝ A z).comp spatialInclusion)
  exact congrArg SpatialCurl.curlLinear hd

/-- Taking the actual spatial curl costs exactly one joint derivative
and a fixed linear-operator norm. -/
theorem spatialCurl_jet_bound {A : ProblemStatement.VelocityField}
    {U : Set ProblemStatement.SpaceTime} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    {z : ProblemStatement.SpaceTime} (hz : z ∈ U) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl A) z‖ ≤
      ‖jointCurl‖ * ‖iteratedFDeriv ℝ (m + 1) A z‖ := by
  have he : SpatialCurl.spatialCurl A =ᶠ[𝓝 z] jointCurl ∘ fderiv ℝ A := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact spatialCurl_eq_joint ((hA.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq he m]
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ A) z :=
    (hA.contDiffAt (hU.mem_nhds hz)).fderiv_right (by simp)
  have hb := PhysicalWaveSum.norm_jet_linear_comp_at (hd.of_le (nat_le_infty m)) jointCurl
  simpa only [norm_iteratedFDeriv_fderiv] using hb

theorem physical_vector_curl_jet_bound {s : StripData D} {h α σ a b r0 Z P : ℝ}
    {w : ι → ℕ → D → ℝ} {f : ι → ℕ → D → ℂ}
    (hf : SourceBounds s h α w f) {H Δ : ℕ} {F : Fin 3 → PhysicalWaveSum.WaveFamily H}
    (hc : ∀ i, CommonChart (F i) a b h r0 σ f)
    (hb : ∀ i, CarrierBounds (F i) a b h r0)
    (hr : ∀ i, PhysicalWaveSum.RegularFamily (F i) a b h r0 Z Δ)
    (hh : 0 < h) (hh1 : h < 1 / 2) (ha : 0 < a) (hZ : 0 ≤ Z) (hr0 : 0 ≤ r0)
    (hP : 1 ≤ P) (hp : ∀ i L, |((F i).carrier L).angular| ≤ P ∧
      |((F i).carrier L).axial| ≤ P ∧ |((F i).carrier L).radial| ≤ P) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ProblemStatement.SpaceTime,
      z ∈ PhysicalWaveSum.preterminal → |z.1| ≤ 1 →
      ‖iteratedFDeriv ℝ m (SpatialCurl.spatialCurl (PhysicalWaveSum.vectorSum F a h r0)) z‖ ≤
        C * PhysicalWaveSum.physicalQ h z ^ (h * α - physicalLoss h σ (m + 1)) := by
  obtain ⟨C, hC, hbound⟩ := physical_vector_sum_jet_bound hf hc hb hr
    hh hh1 ha hZ hr0 hP hp (m + 1)
  refine ⟨‖jointCurl‖ * C, mul_nonneg (norm_nonneg jointCurl) hC, ?_⟩
  intro z hz ht
  exact (spatialCurl_jet_bound PhysicalWaveSum.preterminal_open
    (PhysicalWaveSum.vectorSum_smooth hr ha hh hh1) hz m).trans
      ((mul_le_mul_of_nonneg_left (hbound z hz ht) (norm_nonneg jointCurl)).trans_eq (by ring))

@[simp] theorem physicalLoss_potential (h : ℝ) (m : ℕ) :
    physicalLoss h (-h) m = PhysicalGraphBounds.waveLoss h m + h := by
  simp [physicalLoss]

@[simp] theorem physicalLoss_velocity (h : ℝ) (m : ℕ) :
    physicalLoss h (-CoordinateAlgebra.A h) m =
      PhysicalGraphBounds.waveLoss h m + CoordinateAlgebra.A h := by
  simp [physicalLoss]

@[simp] theorem physicalLoss_pressure (h : ℝ) (m : ℕ) :
    physicalLoss h (-(2 * CoordinateAlgebra.A h)) m =
      PhysicalGraphBounds.waveLoss h m + 2 * CoordinateAlgebra.A h := by
  simp [physicalLoss]

/-! ### The actual Cartesian-to-cylindrical coefficient map -/

abbrev CylindricalPoint := ℝ × ((ℝ × ℝ) × PhysicalGraphBounds.Plane)

noncomputable def cartesianRadius (y : PhysicalGraphBounds.Plane) : ℝ :=
  Real.sqrt (y.1 ^ 2 + y.2 ^ 2)

theorem cartesianRadius_smooth :
    ContDiffOn ℝ ∞ cartesianRadius {y : PhysicalGraphBounds.Plane | y ≠ 0} := by
  intro y hy
  exact (((contDiffAt_fst.pow 2).add (contDiffAt_snd.pow 2)).sqrt
    (PhysicalGraphBounds.sum_sq_pos hy).ne').contDiffWithinAt

/-- Slow order `(T,Z)` and the actual common auxiliary coordinate. -/
noncomputable def slowFast : PhysicalWaveSum.LiftPoint →L[ℝ]
    ((ℝ × ℝ) × PhysicalGraphBounds.Plane) :=
  (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp PhysicalGraphBounds.liftZT).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp PhysicalGraphBounds.liftZT)).prod
    (ContinuousLinearMap.snd ℝ PhysicalGraphBounds.ChartPoint PhysicalGraphBounds.Plane)

@[simp] theorem slowFast_apply (x : PhysicalWaveSum.LiftPoint) :
    slowFast x = ((x.1.1, x.1.2.2.2), x.2) := rfl

theorem norm_slowFast_le : ‖slowFast‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  rw [one_mul, slowFast_apply]
  change max (max ‖x.1.1‖ ‖x.1.2.2.2‖) ‖x.2‖ ≤ ‖x‖
  exact max_le (max_le
    ((le_max_left ‖x.1.1‖ ‖x.1.2‖).trans (le_max_left _ _))
    ((le_max_right ‖x.1.2.2.1‖ ‖x.1.2.2.2‖).trans
      ((le_max_right ‖x.1.2.1‖ ‖x.1.2.2‖).trans
        ((le_max_right ‖x.1.1‖ ‖x.1.2‖).trans (le_max_left _ _)))))
    (le_max_right _ _)

noncomputable def cylindricalMap (x : PhysicalWaveSum.LiftPoint) : CylindricalPoint :=
  (cartesianRadius (PhysicalGraphBounds.liftXY x), slowFast x)

noncomputable def cylindricalDomain (a b : ℝ) : Set PhysicalWaveSum.LiftPoint :=
  (fun x => ‖PhysicalGraphBounds.liftXY x‖) ⁻¹' Ioo (a / 2) (b + 1)

theorem cylindricalDomain_open (a b : ℝ) : IsOpen (cylindricalDomain a b) :=
  isOpen_Ioo.preimage PhysicalGraphBounds.liftXY.continuous.norm

theorem cylindricalDomain_axisFree {a b : ℝ} (ha : 0 < a)
    {x : PhysicalWaveSum.LiftPoint} (hx : x ∈ cylindricalDomain a b) :
    PhysicalGraphBounds.liftXY x ≠ 0 := by
  intro he
  have hp : a / 2 < ‖PhysicalGraphBounds.liftXY x‖ := hx.1
  rw [he, norm_zero] at hp
  linarith

theorem cylindricalMap_smooth {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ cylindricalMap (cylindricalDomain a b) :=
  (cartesianRadius_smooth.comp PhysicalGraphBounds.liftXY.contDiff.contDiffOn
    (fun _ hx => cylindricalDomain_axisFree ha hx)).prodMk slowFast.contDiff.contDiffOn

/-- All positive jets of the actual radius map are uniformly bounded on
a fixed padded annulus, regardless of slow or auxiliary coordinates. -/
theorem cylindricalMap_positiveJets {a b : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ cylindricalDomain a b, ∀ j, 1 ≤ j → j ≤ m →
      ‖iteratedFDeriv ℝ j cylindricalMap x‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := PhysicalGraphBounds.compact_jet_bound
    PhysicalGraphBounds.axisFree_open cartesianRadius_smooth
    (PhysicalGraphBounds.isCompact_annulus (a / 2) (b + 1))
    (PhysicalGraphBounds.annulus_axisFree (half_pos ha)) m
  refine ⟨B, hB, ?_⟩
  intro x hx j hj hjm
  have haxis := cylindricalDomain_axisFree ha hx
  have hann : PhysicalGraphBounds.liftXY x ∈ PhysicalGraphBounds.annulus (a / 2) (b + 1) := by
    refine ⟨?_, hx.1.le⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2.le
  have hrad : ContDiffAt ℝ ∞ (cartesianRadius ∘ PhysicalGraphBounds.liftXY) x :=
    (cartesianRadius_smooth.contDiffAt (PhysicalGraphBounds.axisFree_open.mem_nhds haxis)).comp x
      PhysicalGraphBounds.liftXY.contDiff.contDiffAt
  have hrb : ‖iteratedFDeriv ℝ j (cartesianRadius ∘ PhysicalGraphBounds.liftXY) x‖ ≤ B := by
    exact (PhysicalGraphBounds.norm_jet_comp_linear PhysicalGraphBounds.axisFree_open
      cartesianRadius_smooth PhysicalGraphBounds.liftXY haxis j).trans
      ((mul_le_mul (hb j hjm _ hann)
        (pow_le_one₀ (norm_nonneg _) PhysicalGraphBounds.norm_liftXY_le)
        (by positivity) (zero_le_one.trans hB)).trans_eq (mul_one B))
  change ‖iteratedFDeriv ℝ j
    (fun y => ((cartesianRadius ∘ PhysicalGraphBounds.liftXY) y, slowFast y)) x‖ ≤ B
  rw [PhysicalGraphBounds.iteratedFDeriv_pair (hrad.of_le (nat_le_infty j))
    (slowFast.contDiff.contDiffAt.of_le (nat_le_infty j)), ContinuousMultilinearMap.opNorm_prod]
  exact max_le hrb ((PhysicalGraphBounds.norm_positive_jet_linear_le slowFast x hj).trans
    (norm_slowFast_le.trans hB))

@[simp] theorem liftXY_commonLift (h : ℝ) (n d : ℕ) (z : ProblemStatement.SpaceTime) :
    PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d z) =
      PhysicalGraphBounds.scaledRadial n z := by
  change PhysicalGraphBounds.liftXY (PhysicalGraphBounds.physicalLift h n z) = _
  exact PhysicalGraphBounds.liftXY_physicalLift h n z

/-- The actual common graph has the expected cylindrical radius, scaled
slow variables, and inverse-covered auxiliary coordinate. -/
theorem cylindricalMap_commonLift (h : ℝ) (n d : ℕ) (z : ProblemStatement.SpaceTime) :
    cylindricalMap (PhysicalWaveSum.commonLift h n d z) =
      (cartesianRadius (PhysicalGraphBounds.scaledRadial n z),
        (((1 - z.1) / ChartScales.Q n, ChartScales.Q n ^ (-CoordinateAlgebra.D h) * z.2 2),
          (CommonCoverSolve.coverPower d).symm (PhysicalGraphBounds.nativeGraph h n z))) := by
  rw [cylindricalMap, liftXY_commonLift, slowFast_apply]
  simp only [PhysicalWaveSum.commonLift, Function.comp_apply, PhysicalWaveSum.downLift_apply,
    PhysicalGraphBounds.physicalLift, PhysicalGraphBounds.physicalChart_time]
  simp [PhysicalGraphBounds.physicalChart, PhysicalGraphBounds.chartLinear_apply]

theorem commonLift_mem_cylindricalDomain {a b : ℝ} (ha : 0 < a)
    (h : ℝ) (n d : ℕ) (z : ProblemStatement.SpaceTime)
    (hz : PhysicalGraphBounds.scaledRadial n z ∈ PhysicalGraphBounds.annulus a b) :
    PhysicalWaveSum.commonLift h n d z ∈ cylindricalDomain a b := by
  change a / 2 < ‖PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d z)‖ ∧
    ‖PhysicalGraphBounds.liftXY (PhysicalWaveSum.commonLift h n d z)‖ < b + 1
  rw [liftXY_commonLift]
  have hlo : a ≤ ‖PhysicalGraphBounds.scaledRadial n z‖ := hz.2
  have hhi : ‖PhysicalGraphBounds.scaledRadial n z‖ ≤ b := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  constructor <;> linarith

/-- Direct adapter for a genuine cylindrical coefficient.  No coordinate
derivative estimate is assumed: the preceding theorems prove it. -/
noncomputable def cylindricalCommonChart {H : ℕ} (F : PhysicalWaveSum.WaveFamily H)
    (a b h r0 σ : ℝ) (ha : 0 < a) (f : ι → ℕ → CylindricalPoint → ℂ)
    (index : PhysicalWaveSum.WaveIndex H → ι)
    (he : ∀ I, F.amplitude I = fun x =>
      (ChartScales.Q I.1.val.1 ^ σ) • f (index I) I.1.val.1 (cylindricalMap x)) :
    CommonChart F a b h r0 σ f where
  sourceIndex := index
  map _ := cylindricalMap
  domain _ := cylindricalDomain a b
  open_domain _ := cylindricalDomain_open a b
  smooth _ := cylindricalMap_smooth ha
  positive_jets m := by
    obtain ⟨B, hB, hb⟩ := cylindricalMap_positiveJets (b := b) ha m
    exact ⟨B, hB, 0, fun _ x hx j hj hjm => by simpa using hb x hx j hj hjm⟩
  amplitude_eq := he
  contains I z _ _ hz := commonLift_mem_cylindricalDomain ha h I.1.val.1 (F.gap I.1) z hz

end NavierStokes.PhysicalClassBounds
