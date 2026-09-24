/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.BallCover
public import LeanPool.CaffarelliKohnNirenberg.Setting.ExtSobolevBallTime
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic

/-!
# The velocity is locally `L^{10/3}`, hence locally `L³`

The data clauses of `def:sws` place the velocity in `L^∞_t L²_x ∩ L²_t H¹_x` on
every local box.  Two of the terms of the local energy inequality - the cubic
term `|u|² u · ∇ψ` and the pressure term `p u · ∇ψ` - are not integrable for a
field that is merely square integrable, so those two terms need the parabolic
interpolation

`L^∞_t L²_x ∩ L²_t Ḣ¹_x ↪ L^{10/3}_{t,x}`,

which is the content of `CKN.ball_time_sobolev`.  This file turns that estimate
into the three local statements the energy inequality actually consumes: the
velocity is cubed-integrable, the pressure times the velocity is integrable, and
the force times the velocity is integrable, all on an arbitrary compact subset of
the space-time carrier.

Two features of the interpolation shape the file.

* It lives on Euclidean balls, because the spatial factor of a local box is an
  arbitrary open set and carries no Sobolev extension.  The reduction to balls is
  `CKN.exists_localBox_ball_cover_of_data`; the time factor of the box is used
  unchanged, since the interpolation accepts any order-connected time set.
* Its hypothesis on spatial slices asks for a genuine `CKN.H1Function` on the
  ball for almost every time.  The data clauses give an almost-everywhere weak
  gradient on the box and, after a slicing argument for the joint energy, an
  almost-everywhere square-integrable slice; those two are assembled here into
  the required slice representative and restricted to the ball.

Everything below takes `CKN.IsSuitableWeakSolutionData`, never the full class, so
these lemmas may be used while the integrability clauses of `def:sws` are still
being established.

The sup norm `‖·‖` of `Vec3` is the one the data clauses use, while the energy
density of the paper is the Euclidean norm `CKN.Foundation.Parabolic.vec3EuclideanNorm`.
Both comparisons needed here are the easy direction of the equivalence of the two
norms: a component is bounded by the sup norm on the way into the interpolation,
and the Euclidean norm is bounded by `√3` times the sup norm on the way out.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-! ### Exponents

The data clauses record the pressure exponent as `ENNReal.ofReal (3 / 2)` and the
interpolation records its own exponent as `ENNReal.ofReal (10 / 3)`, while the
Hölder machinery of Mathlib is stated for extended-real numerals.  The two
bridges below and the Hölder pairing `3 / 2` with `3` are what connect them;
Mathlib supplies no such pairing for these numerals. -/

/-- The pressure exponent of `def:sws` as an extended-real numeral. -/
theorem ofReal_threeHalves : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
  rw [show (3 / 2 : ℝ) = ((3 : ℝ) / 2) by norm_num]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- The velocity exponent used below as an extended-real numeral. -/
theorem ofReal_three : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by simp

/-- Hölder's inequality pairs `L^{3/2}` with `L³` to give `L¹`, because
`2 / 3 + 1 / 3 = 1`.  This is the pairing behind both the pressure term and the
force term of the local energy inequality. -/
instance holderTriple_threeHalves_three :
    ENNReal.HolderTriple (3 / 2 : ℝ≥0∞) (3 : ℝ≥0∞) 1 where
  inv_add_inv_eq_inv := by
    rw [show ((3 : ℝ≥0∞) / 2)⁻¹ = 2 / 3 by
      rw [ENNReal.inv_div (by norm_num) (by norm_num)]]
    rw [show (3 : ℝ≥0∞)⁻¹ = 1 / 3 by rw [one_div]]
    rw [ENNReal.div_add_div_same]
    rw [show (2 : ℝ≥0∞) + 1 = 3 by norm_num]
    rw [inv_one]
    exact ENNReal.div_self (a := (3 : ℝ≥0∞)) (by norm_num) (by norm_num)

/-! ### `L^p` membership through the Lebesgue integral

The data clauses state their finiteness with Lebesgue integrals of powers of the
extended norm, whereas the interpolation and Hölder's inequality both speak of
`MeasureTheory.MemLp`.  The two are the same statement for a finite exponent, and
the translations are collected here once. -/

/-- A measurable field whose squared extended norm has finite integral is square
integrable. -/
private theorem memLp_two_of_lintegral_lt_top {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {v : α → E}
    (hv : AEStronglyMeasurable v μ) (hlt : (∫⁻ z, ‖v z‖ₑ ^ (2 : ℝ) ∂μ) < ⊤) :
    MemLp v 2 μ := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hv]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hlt.ne

/-- A measurable field whose `t`-th power of the extended norm has finite
integral belongs to `L^t`, for a positive real exponent `t`. -/
private theorem memLp_ofReal_of_lintegral_lt_top {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {t : ℝ} (ht : 0 < t) {v : α → E}
    (hv : AEStronglyMeasurable v μ) (hlt : (∫⁻ z, ‖v z‖ₑ ^ t ∂μ) < ⊤) :
    MemLp v (ENNReal.ofReal t) μ := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by simpa using ht) ENNReal.ofReal_ne_top hv,
    ENNReal.toReal_ofReal ht.le]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hlt.ne

/-- The converse translation: membership in `L^t` for a positive real exponent
gives a finite integral of the `t`-th power of the extended norm. -/
private theorem lintegral_lt_top_of_memLp_ofReal {α E : Type} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {t : ℝ} (ht : 0 < t) {v : α → E}
    (hv : MemLp v (ENNReal.ofReal t) μ) :
    (∫⁻ z, ‖v z‖ₑ ^ t ∂μ) < ⊤ := by
  have hmeas := hv.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by simpa using ht) ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal ht.le] at hv
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.top_rpow_of_pos (by positivity)] at hv
  exact absurd hv (lt_irrefl _)

/-- A Lebesgue integral over a set covered by finitely many sets of finite
integral is itself finite.  This is how the ball cover is glued. -/
private theorem lintegral_lt_top_of_finite_cover {n : ℕ}
    {S : Fin n → Set ParabolicPoint} {K : Set ParabolicPoint}
    (hK : K ⊆ ⋃ m, S m) {g : ParabolicPoint → ℝ≥0∞}
    (h : ∀ m, (∫⁻ z in S m, g z) < ⊤) :
    (∫⁻ z in K, g z) < ⊤ := by
  calc (∫⁻ z in K, g z) ≤ ∫⁻ z in ⋃ m, S m, g z := lintegral_mono_set hK
    _ ≤ ∑' m, ∫⁻ z in S m, g z := lintegral_iUnion_le _ _
    _ = ∑ m, ∫⁻ z in S m, g z := tsum_fintype _
    _ < ⊤ := ENNReal.sum_lt_top.mpr fun m _ => h m

/-- A cylinder over a subset of the spatial factor of a local box carries a
finite measure, because both factors of the box have compact closure.  Lowering
an exponent on such a cylinder is Hölder's inequality against this measure. -/
private theorem isFiniteMeasure_restrict_ballBox {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox Ω I Ω' J) {U : Set Vec3} (hU : U ⊆ Ω') :
    IsFiniteMeasure (volume.restrict (spaceTimeSet U J)) := by
  refine isFiniteMeasure_restrict.mpr ?_
  have hcpt : IsCompact ((closure Ω') ×ˢ (closure J)) := hbox.2.1.prod hbox.2.2.2.2.1
  have hsub : (show Set (Vec3 × ℝ) from spaceTimeSet U J) ⊆ (closure Ω') ×ˢ (closure J) :=
    Set.prod_mono (hU.trans subset_closure) subset_closure
  have hlt : (volume : Measure (Vec3 × ℝ)) (show Set (Vec3 × ℝ) from spaceTimeSet U J) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) hcpt.measure_lt_top
  exact hlt.ne

/-- A component of a vector has extended norm at most that of the vector: the
norm of `Vec3` is the supremum of the absolute values of the components. -/
private theorem enorm_apply_le (v : Vec3) (i : Fin 3) : ‖v i‖ₑ ≤ ‖v‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm v i)

/-- A measurable field of finite energy has integrable squared norm. -/
private theorem integrable_sq_of_lintegral_lt_top {E : Type} [NormedAddCommGroup E]
    {S : Set ParabolicPoint} {v : ParabolicPoint → E}
    (hv : AEStronglyMeasurable v (volume.restrict S))
    (hvlt : (∫⁻ z in S, ‖v z‖ₑ ^ (2 : ℝ)) < ⊤) :
    Integrable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ)) (volume.restrict S) := by
  have hvmeas : AEStronglyMeasurable (fun z => (‖v z‖ : ℝ) ^ (2 : ℕ))
      (volume.restrict S) := hv.norm.pow 2
  have hvfin : (∫⁻ z in S, ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun z => ?_)) hvlt)
    calc
      ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℕ))
          = ENNReal.ofReal ((‖v z‖ : ℝ) ^ (2 : ℝ)) := by
            norm_num [Real.rpow_natCast]
      _ = ENNReal.ofReal ‖v z‖ ^ (2 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)).symm
      _ = ‖v z‖ₑ ^ (2 : ℝ) := by rw [ofReal_norm]
  exact (lintegral_ofReal_ne_top_iff_integrable hvmeas
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hvfin

/-! ### Spatial slices of the velocity

The interpolation is proved slice by slice in time, so it asks for a spatial
Sobolev representative at almost every time.  The data clauses give the joint
finiteness of the energy on the box and an almost-everywhere weak gradient on the
box; the first is turned into almost-everywhere square integrability of the
slices by the product structure of Lebesgue measure on space-time, and the two
are then combined. -/

/-- Almost every spatial slice of the velocity and of its gradient is square
integrable on the spatial factor of a local box. -/
private theorem slice_memLp_two_ae_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J) :
    ∀ᵐ s ∂volume.restrict J,
      MemLp (fun x : Vec3 => u (x, s)) 2 (volume.restrict Ω') ∧
      MemLp (fun x : Vec3 => Du (x, s)) 2 (volume.restrict Ω') := by
  have hu := hdata.aestronglyMeasurable_velocity hbox
  have hDu := hdata.aestronglyMeasurable_gradient hbox
  have henergy := hdata.energy_lintegral_lt_top hbox
  have hu_lt : (∫⁻ z in spaceTimeSet Ω' J, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun _ => le_add_right le_rfl) henergy
  have hDu_lt : (∫⁻ z in spaceTimeSet Ω' J, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun _ => le_add_left le_rfl) henergy
  have hu_sq : Integrable (fun z => (‖u z‖ : ℝ) ^ (2 : ℕ))
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact integrable_sq_of_lintegral_lt_top hu hu_lt
  have hDu_sq : Integrable (fun z => (‖Du z‖ : ℝ) ^ (2 : ℕ))
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact integrable_sq_of_lintegral_lt_top hDu hDu_lt
  have hu_meas : AEStronglyMeasurable u
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]; exact hu
  have hDu_meas : AEStronglyMeasurable Du
      (((volume : Measure Vec3).restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]; exact hDu
  filter_upwards [hu_meas.prodMk_right, hDu_meas.prodMk_right,
    hu_sq.prod_left_ae, hDu_sq.prod_left_ae]
    with s hus hDus husq hDusq
  exact ⟨(memLp_two_iff_integrable_sq_norm hus).2 husq,
    (memLp_two_iff_integrable_sq_norm hDus).2 hDusq⟩

/-- Almost every spatial slice of a velocity component is represented by an
`CKN.H1Function` on a ball of the spatial factor of a local box.  This is the
slice hypothesis of `CKN.ball_time_sobolev`; the representative is the slice
itself, so the two almost-everywhere identifications are reflexivity. -/
private theorem slice_h1_ae_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    {x₀ : Vec3} {r : ℝ} (hball : vec3Ball x₀ r ⊆ Ω') (i : Fin 3) :
    ∀ᵐ s ∂volume.restrict J, ∃ v : H1Function (vec3Ball x₀ r),
      (fun x => u (x, s) i) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.toFun ∧
      (fun x => Du (x, s) i) =ᵐ[volume.restrict (vec3Ball x₀ r)] v.grad := by
  filter_upwards [slice_memLp_two_ae_of_data hdata hbox,
    hdata.hasWeakGradientOn_slice hbox i] with s hmem hgrad
  refine ⟨⟨fun x => u (x, s) i, fun x => Du (x, s) i, ?_, fun j => ?_, ?_⟩,
    Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
  · exact (memLp_pi_iff.mp hmem.1 i).mono_measure (Measure.restrict_mono hball le_rfl)
  · exact (memLp_pi_iff.mp (memLp_pi_iff.mp hmem.2 i) j).mono_measure
      (Measure.restrict_mono hball le_rfl)
  · exact hgrad.restrict (isOpen_vec3Ball x₀ r) hball

/-- The spatial `L²` norms of the slices of a velocity component are essentially
bounded in time on a ball of the spatial factor of a local box.  This is the
`L^∞_t L²_x` hypothesis of `CKN.ball_time_sobolev`, read off from the slice
energy bound of the data clauses. -/
private theorem essSup_slice_eLpNorm_lt_top_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    {x₀ : Vec3} {r : ℝ} (hball : vec3Ball x₀ r ⊆ Ω') (i : Fin 3) :
    essSup (fun s => eLpNorm (fun x => u (x, s) i) 2
        (volume.restrict (vec3Ball x₀ r))) (volume.restrict J) < ⊤ := by
  set B := essSup (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict J) with hBdef
  have hB : B < ⊤ := hdata.essSup_sliceEnergy_lt_top hbox
  have hae : ∀ᵐ s ∂volume.restrict J,
      eLpNorm (fun x => u (x, s) i) 2 (volume.restrict (vec3Ball x₀ r)) ≤
        B ^ (1 / 2 : ℝ) := by
    filter_upwards [ENNReal.ae_le_essSup
        (μ := volume.restrict J) (fun s => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)),
      slice_memLp_two_ae_of_data hdata hbox] with s hs hmem
    have hmeas : AEStronglyMeasurable (fun x => u (x, s) i)
        (volume.restrict (vec3Ball x₀ r)) :=
      ((memLp_pi_iff.mp hmem.1 i).mono_measure
        (Measure.restrict_mono hball le_rfl)).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmeas]
    simp only [ENNReal.toReal_ofNat]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc (∫⁻ x in vec3Ball x₀ r, ‖u (x, s) i‖ₑ ^ (2 : ℝ))
        ≤ ∫⁻ x in Ω', ‖u (x, s) i‖ₑ ^ (2 : ℝ) := lintegral_mono_set hball
      _ ≤ ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ) :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (enorm_apply_le _ i) (by norm_num)
      _ ≤ B := hs
  exact lt_of_le_of_lt (essSup_le_of_ae_le _ hae)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hB.ne)

/-! ### The interpolation on one ball cylinder -/

/-- Each velocity component is `L^{10/3}` on a cylinder whose spatial factor is a
ball inside the spatial factor of a local box and whose time factor is the time
factor of that box.  This is `CKN.ball_time_sobolev` applied componentwise; the
hypothesis that a component is square integrable costs nothing, because a
component is bounded by the supremum norm the data clauses control. -/
theorem velocity_component_memLp_tenThirds_on_ballBox_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) (hball : vec3Ball x₀ r ⊆ Ω')
    (i : Fin 3) :
    MemLp (fun z : ParabolicPoint => u z i) (ENNReal.ofReal (10 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball x₀ r) J)) := by
  have hsub : spaceTimeSet (vec3Ball x₀ r) J ⊆ spaceTimeSet Ω' J :=
    Set.prod_mono hball le_rfl
  have henergy := hdata.energy_lintegral_lt_top hbox
  have hu2box : MemLp u 2 (volume.restrict (spaceTimeSet Ω' J)) :=
    memLp_two_of_lintegral_lt_top (hdata.aestronglyMeasurable_velocity hbox)
      (lt_of_le_of_lt (lintegral_mono fun _ => le_add_right le_rfl) henergy)
  have hDu2box : MemLp Du 2 (volume.restrict (spaceTimeSet Ω' J)) :=
    memLp_two_of_lintegral_lt_top (hdata.aestronglyMeasurable_gradient hbox)
      (lt_of_le_of_lt (lintegral_mono fun _ => le_add_left le_rfl) henergy)
  have hu2 : MemLp (fun z : ParabolicPoint => u z i) 2
      (volume.restrict (spaceTimeSet (vec3Ball x₀ r) J)) :=
    memLp_pi_iff.mp (hu2box.mono_measure (Measure.restrict_mono hsub le_rfl)) i
  have hDu2 : MemLp (fun z : ParabolicPoint => Du z i) 2
      (volume.restrict (spaceTimeSet (vec3Ball x₀ r) J)) :=
    memLp_pi_iff.mp (hDu2box.mono_measure (Measure.restrict_mono hsub le_rfl)) i
  obtain ⟨_C, _hC, hmain⟩ := ball_time_sobolev
  exact (hmain x₀ r hr J hbox.2.2.2.1 (fun z => u z i) (fun z => Du z i)
    hu2.aestronglyMeasurable hDu2.aestronglyMeasurable
    (slice_h1_ae_of_data hdata hbox hball i) hu2 hDu2
    (essSup_slice_eLpNorm_lt_top_of_data hdata hbox hball i)).1

/-! ### Cubic integrability on a compact set -/

/-- The velocity is `L³` on every compact subset of the space-time carrier.  The
compact set is covered by finitely many ball cylinders of one local box, each
cylinder carries the `L^{10/3}` bound of the interpolation, and each cylinder has
finite measure, so the exponent drops from `10 / 3` to `3` there; the finitely
many bounds are then added. -/
theorem velocity_memLp_three_on_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    MemLp u (ENNReal.ofReal (3 : ℝ)) (volume.restrict K) := by
  obtain ⟨Ω', J, n, c, rad, hbox, hradpos, hradsub, hcov⟩ :=
    exists_localBox_ball_cover_of_data hdata hK hKsub
  refine memLp_ofReal_of_lintegral_lt_top (by norm_num)
    (velocity_memLp_two_on_compact_of_data hdata hK hKsub).aestronglyMeasurable ?_
  refine lintegral_lt_top_of_finite_cover hcov fun m => ?_
  have hfin := isFiniteMeasure_restrict_ballBox hbox (hradsub m)
  have hpi : MemLp u (ENNReal.ofReal (3 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (c m) (rad m)) J)) := by
    refine memLp_pi_iff.mpr fun i => ?_
    exact (velocity_component_memLp_tenThirds_on_ballBox_of_data hdata hbox
      (hradpos m) (hradsub m) i).mono_exponent
        (ENNReal.ofReal_le_ofReal (by norm_num))
  exact lintegral_lt_top_of_memLp_ofReal (by norm_num) hpi

/-- The cube of the Euclidean norm is bounded by `3 √3` times the cube of the
supremum norm, in extended arithmetic. -/
private theorem ofReal_vec3EuclideanNorm_cube_le (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v ^ (3 : ℕ)) ≤
      ENNReal.ofReal (3 * Real.sqrt 3) * ‖v‖ₑ ^ (3 : ℝ) := by
  have hcube : vec3EuclideanNorm v ^ (3 : ℕ) ≤ (3 * Real.sqrt 3) * ‖v‖ ^ (3 : ℕ) := by
    have hle := vec3EuclideanNorm_le_sqrt_three_mul_norm v
    have hpow : vec3EuclideanNorm v ^ (3 : ℕ) ≤ (Real.sqrt 3 * ‖v‖) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (vec3EuclideanNorm_nonneg v) hle 3
    have hexp : (Real.sqrt 3 * ‖v‖) ^ (3 : ℕ) = (3 * Real.sqrt 3) * ‖v‖ ^ (3 : ℕ) := by
      have hs : Real.sqrt 3 ^ (2 : ℕ) = 3 := Real.sq_sqrt (by norm_num)
      calc (Real.sqrt 3 * ‖v‖) ^ (3 : ℕ)
          = (Real.sqrt 3 ^ (2 : ℕ) * Real.sqrt 3) * ‖v‖ ^ (3 : ℕ) := by ring
        _ = (3 * Real.sqrt 3) * ‖v‖ ^ (3 : ℕ) := by rw [hs]
    exact hpow.trans (le_of_eq hexp)
  calc ENNReal.ofReal (vec3EuclideanNorm v ^ (3 : ℕ))
      ≤ ENNReal.ofReal ((3 * Real.sqrt 3) * ‖v‖ ^ (3 : ℕ)) :=
        ENNReal.ofReal_le_ofReal hcube
    _ = ENNReal.ofReal (3 * Real.sqrt 3) * ‖v‖ₑ ^ (3 : ℝ) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
        norm_num [Real.rpow_natCast]

/-- The cube of the Euclidean norm of the velocity, which is the density of the
cubic term of the local energy inequality, is integrable on every compact subset
of the space-time carrier. -/
theorem velocity_cube_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun z => vec3EuclideanNorm (u z) ^ (3 : ℕ)) K volume := by
  have hu3 := velocity_memLp_three_on_compact_of_data hdata hK hKsub
  have hint : (∫⁻ z in K, ‖u z‖ₑ ^ (3 : ℝ)) < ⊤ :=
    lintegral_lt_top_of_memLp_ofReal (by norm_num) hu3
  have hmeas : AEStronglyMeasurable
      (fun z : ParabolicPoint => vec3EuclideanNorm (u z) ^ (3 : ℕ)) (volume.restrict K) :=
    (continuous_vec3EuclideanNorm.pow 3).comp_aestronglyMeasurable
      hu3.aestronglyMeasurable
  have hfin : (∫⁻ z in K, ENNReal.ofReal (vec3EuclideanNorm (u z) ^ (3 : ℕ))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt
      (lintegral_mono fun z => ofReal_vec3EuclideanNorm_cube_le (u z)) ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint
  refine (lintegral_ofReal_ne_top_iff_integrable hmeas ?_).mp hfin
  exact Filter.Eventually.of_forall fun z => pow_nonneg (vec3EuclideanNorm_nonneg _) 3

/-! ### The two Hölder pairings against the velocity -/

/-- The pressure times a velocity component is integrable on every compact subset
of the space-time carrier: the pressure is `L^{3/2}` by the data clauses and the
velocity is `L³` by the interpolation. -/
theorem pressure_mul_velocity_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I)
    (i : Fin 3) :
    IntegrableOn (fun z => p z * u z i) K volume := by
  have hp := pressure_memLp_threeHalves_on_compact_of_data hdata hK hKsub
  have hui := memLp_pi_iff.mp (velocity_memLp_three_on_compact_of_data hdata hK hKsub) i
  rw [ofReal_threeHalves] at hp
  rw [ofReal_three] at hui
  exact hp.integrable_mul hui

/-- A force component times a velocity component is integrable on every compact
subset of the space-time carrier.  The force exponent of `def:sws` exceeds
`5 / 2`, hence exceeds `3 / 2`, and the compact set has finite measure, so the
same `3 / 2` with `3` pairing applies. -/
theorem force_mul_velocity_integrableOn_compact_of_data
    (hdata : IsSuitableWeakSolutionData Ω I q u Du p f)
    {K : Set ParabolicPoint} (hK : IsCompact K) (hKsub : K ⊆ spaceTimeSet Ω I)
    (i j : Fin 3) :
    IntegrableOn (fun z => f z i * u z j) K volume := by
  have := isFiniteMeasure_restrict_of_isCompact hK
  have hfi := memLp_pi_iff.mp (force_memLp_on_compact_of_data hdata hK hKsub) i
  have hf32 : MemLp (fun z : ParabolicPoint => f z i) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict K) :=
    hfi.mono_exponent (ENNReal.ofReal_le_ofReal
      (by linarith only [hdata.five_halves_lt_exponent]))
  have huj := memLp_pi_iff.mp (velocity_memLp_three_on_compact_of_data hdata hK hKsub) j
  rw [ofReal_threeHalves] at hf32
  rw [ofReal_three] at huj
  exact hf32.integrable_mul huj

end CKN
