/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.DenseTime.CemeterySemigroup
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelEquivariance
import LeanPool.MarkovProcess.MarkovProcess.Killed.Process

/-!
# Finite-dimensional distributions of the killed process

For the continuous-path process of a conservative Feller semigroup and an open set `U`, this file
identifies every finite-dimensional distribution of the process killed at the exit of `U`
(`killedProcess P hP U hU` of `Killed/Process.lean`, a law on lifetime paths in the carrier `U`)
with the corresponding finite-dimensional distribution of the **cemetery extension of the killed
semigroup** on `U`:

  `(killedProcess x).map (fun ω ↦ fun i : I ↦ coordinate i ω) =
      finiteSetKernel (cemeterySemigroup (killedSemigroup P hP U hU hFeller hK)) I (alive x)`

(`killedProcess_map_finiteEvaluation`), and, at a strictly increasing family of times, the
corresponding statement for `finiteTimeKernel` (`killedProcess_map_coordinates_ordered`).

The proof is by induction on the number of times, along the recursion of `finiteTimeKernel`.  The
induction step splits the survival event at the first time `t₁`: on `{t₁ < τ_U}` the later
coordinates of the killed path are the coordinates of the killed shifted path
(`coordinate_killAtExit_shift`), and the law of the shifted path is supplied by the restart
statement `continuousProcess_killedEvent_inter_shift` proved here, a form of the Markov property
at `t₁` restricted to the `𝓕_{t₁}`-event `{t₁ < τ_U} ∩ {ω t₁ ∈ B}`; on the complement every
coordinate is the cemetery state, matching the absorbing behaviour of the cemetery
(`finiteTimeKernel_cemeterySemigroup_delta`).  Measures on a finite product are compared on boxes.

No Feller property, strong continuity, or regularity of the killed semigroup is claimed, and no
statement here covers a random time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

section Dead

variable {beta : Type*} [MeasurableSpace beta] (S : SubMarkovKernelSemigroup beta)

/-- Started at the cemetery, every finite-time law of a cemetery extension is the Dirac mass at
the path that is dead at all times: the cemetery is absorbing. -/
theorem finiteTimeKernel_cemeterySemigroup_delta {n : ℕ} (times : FiniteOrderedTimes n) :
    finiteTimeKernel (cemeterySemigroup S) times Cemetery.delta =
      Measure.dirac (fun _ ↦ Cemetery.delta) := by
  induction n with
  | zero =>
      rw [finiteTimeKernel_zero, Kernel.const_apply]
      exact congrArg Measure.dirac (Subsingleton.elim _ _)
  | succ n ih =>
      let : IsMarkovKernel (cemeterySemigroup S (times 0)) :=
        (isConservative_cemeterySemigroup S).isMarkovKernel (times 0)
      let : IsMarkovKernel (finiteTimeKernel (cemeterySemigroup S) times.relativeTail) :=
        (isConservative_cemeterySemigroup S).isMarkovKernel_finiteTimeKernel _ _
      have hprod : (cemeterySemigroup S (times 0) ⊗ₖ
            Kernel.prodMkLeft (Cemetery beta)
              (finiteTimeKernel (cemeterySemigroup S) times.relativeTail))
              Cemetery.delta =
          Measure.dirac (Cemetery.delta, fun _ ↦ Cemetery.delta) := by
        refine Measure.ext fun s hs ↦ ?_
        rw [Kernel.compProd_apply hs, cemeterySemigroup_absorbing,
          lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left' hs _),
          Kernel.prodMkLeft_apply, ih,
          Measure.dirac_apply' _ (measurable_prodMk_left hs), Measure.dirac_apply' _ hs]
        by_cases hmem : ((Cemetery.delta : Cemetery beta),
            (fun _ ↦ Cemetery.delta : Fin n → Cemetery beta)) ∈ s
        · rw [Set.indicator_of_mem hmem,
            Set.indicator_of_mem (Set.mem_preimage.mpr hmem), Pi.one_apply, Pi.one_apply]
        · rw [Set.indicator_of_notMem hmem]
          exact Set.indicator_of_notMem
            (show (fun _ ↦ Cemetery.delta : Fin n → Cemetery beta) ∉
              Prod.mk (Cemetery.delta : Cemetery beta) ⁻¹' s from fun h ↦ hmem h)
            (1 : (Fin n → Cemetery beta) → ℝ≥0∞)
      rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.map_apply _ measurable_finCons, hprod, Measure.map_dirac' measurable_finCons _]
      refine congrArg Measure.dirac ?_
      funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rw [Fin.cons_zero]
      · rw [Fin.cons_succ]

end Dead


section Restart

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- **Restart on a killed event.**  On the event that the process is still in `U` at time `t` and
sits there in `C`, the law of the path shifted by `t` is the law of the process started at the
time-`t` state, averaged over the killed transition kernel on `U`. -/
theorem IsConservative.continuousProcess_killedEvent_inter_shift
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (t : NNReal) (x : U) {C : Set U} (hC : MeasurableSet C)
    {D : Set (ContinuousPath alpha)} (hD : MeasurableSet D) :
    IsConservative.continuousProcess P hP (x : alpha)
        (ContinuousPath.killedEvent U t (Subtype.val '' C) ∩ ContinuousPath.shift t ⁻¹' D) =
      ∫⁻ y in C, IsConservative.continuousProcess P hP (y : alpha) D
        ∂(IsConservative.killedKernelOn P hP U hU t x) := by
  have hE : MeasurableSet (Subtype.val '' C) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurableSet_image.mpr hC
  have hEpre : MeasurableSet ((fun omega : ContinuousPath alpha ↦ omega t) ⁻¹'
      (Subtype.val '' C)) := (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t) hE
  have hg : Measurable fun y : alpha ↦ IsConservative.continuousProcess P hP y D :=
    (IsConservative.continuousProcess P hP).measurable_coe hD
  have hAfilt : MeasurableSet[ContinuousPath.canonicalFiltration (alpha := alpha) t]
      (ContinuousPath.killedEvent U t (Subtype.val '' C)) :=
    (ContinuousPath.measurableSet_lt_exitTime_canonicalFiltration U hU t).inter
      ((ContinuousPath.measurable_coordinateProcess_canonicalFiltration (alpha := alpha) t) hE)
  have hrestart := congrArg (fun mu : Measure (ContinuousPath alpha) ↦ mu D)
    (hFeller.continuousProcess_restrict_map_shift P hP hK (x : alpha) t
      (ContinuousPath.killedEvent U t (Subtype.val '' C)) hAfilt)
  rw [Measure.map_apply (ContinuousPath.measurable_shift_fixed t) hD,
    Measure.restrict_apply ((ContinuousPath.measurable_shift_fixed t) hD),
    Measure.bind_apply hD (Kernel.aemeasurable _)] at hrestart
  have hset : ContinuousPath.killedEvent U t (Subtype.val '' C) =
      ((fun omega : ContinuousPath alpha ↦ omega t) ⁻¹' (Subtype.val '' C)) ∩
        {omega : ContinuousPath alpha | (t : ℝ≥0∞) < ContinuousPath.exitTime U omega} := by
    ext omega
    simp only [ContinuousPath.mem_killedEvent_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_ofPred_eq]
    exact and_comm
  have hcoord : Measurable fun omega : ContinuousPath alpha ↦ omega t :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) t
  rw [Set.inter_comm, hrestart]
  simp only [Kernel.comap_apply, ContinuousPath.coordinateProcess_apply]
  rw [hset, ← Measure.restrict_restrict hEpre, ← setLIntegral_map hE hg hcoord,
    ← IsConservative.killedKernel_eq_map P hP U hU t (x : alpha),
    ← IsConservative.map_val_killedKernelOn P hP U hU t x,
    setLIntegral_map hE hg measurable_subtype_coe,
    Set.preimage_image_eq C Subtype.val_injective]

end Restart


section OrderedMarginals

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- Reading the killed process at a family of fixed times is reading the killed continuous path at
those times. -/
theorem IsConservative.killedProcess_map_coordinates {iota : Type*} (tau : iota → NNReal)
    (x : U) :
    (IsConservative.killedProcess P hP U hU x).map
        (fun omega ↦ fun i ↦ LifetimePath.coordinate (tau i) omega) =
      (IsConservative.continuousProcess P hP (x : alpha)).map
        (fun omega ↦ fun i ↦
          LifetimePath.coordinate (tau i) (ContinuousPath.killAtExit U omega)) := by
  rw [IsConservative.killedProcess_apply P hP U hU x,
    Measure.map_map (LifetimePath.measurable_coordinateFamily tau)
      (ContinuousPath.measurable_killAtExit U hU)]
  rfl

variable [LocallyCompactSpace alpha]
omit [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
private theorem killed_coordinate_survival_event {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) (B : Fin (n + 1) → Set (Cemetery U)) :
(fun omega : ContinuousPath alpha ↦ fun i : Fin (n + 1) ↦
    LifetimePath.coordinate (times i) (ContinuousPath.killAtExit U omega)) ⁻¹'
        Set.univ.pi B ∩ {omega : ContinuousPath alpha |
    ((times 0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} =
    ContinuousPath.killedEvent U (times 0) (Subtype.val '' (Cemetery.alive ⁻¹' (B 0) :
        Set U)) ∩
      ContinuousPath.shift (times 0) ⁻¹' ((fun omega : ContinuousPath alpha ↦ fun i :
          Fin n ↦
      LifetimePath.coordinate (times.relativeTail i)
        (ContinuousPath.killAtExit U omega)) ⁻¹' (Set.univ.pi fun i : Fin n ↦ B i.succ)) := by
  ext omega
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ_pi, Set.mem_ofPred_eq,
    ContinuousPath.mem_killedEvent_iff]
  constructor
  · rintro ⟨hmem, hsurv⟩
    refine ⟨⟨hsurv, ?_⟩, fun i ↦ ?_⟩
    · have h0 := hmem 0
      rw [ContinuousPath.coordinate_killAtExit_of_lt U omega (times 0) hsurv] at h0
      exact (mem_image_val_iff U
        (ContinuousPath.mem_of_lt_exitTime U omega (times 0) hsurv)).mpr h0
    · have hi := hmem i.succ
      rw [← FiniteOrderedTimes.add_relativeTail times i,
        ← ContinuousPath.coordinate_killAtExit_shift U omega (times 0)
          (times.relativeTail i) hsurv] at hi
      exact hi
  · rintro ⟨⟨hsurv, h0⟩, htail⟩
    refine ⟨fun i ↦ ?_, hsurv⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [ContinuousPath.coordinate_killAtExit_of_lt U omega (times 0) hsurv]
      exact (mem_image_val_iff U
        (ContinuousPath.mem_of_lt_exitTime U omega (times 0) hsurv)).mp h0
    · rw [← FiniteOrderedTimes.add_relativeTail times j,
        ← ContinuousPath.coordinate_killAtExit_shift U omega (times 0)
          (times.relativeTail j) hsurv]
      exact htail j

variable (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)

/-- **Finite-dimensional distributions of the killed process, at ordered times.**  Read at a
strictly increasing family of times, the process killed at the exit of `U` and started at `x ∈ U`
has the finite-time law of the cemetery extension of the killed semigroup on `U`, started at the
live state `x`. -/
theorem IsConservative.killedProcess_map_coordinates_ordered {n : ℕ}
    (times : FiniteOrderedTimes n) (x : U) :
    (IsConservative.killedProcess P hP U hU x).map
        (fun omega ↦ fun i : Fin n ↦ LifetimePath.coordinate (times i) omega) =
      finiteTimeKernel (cemeterySemigroup (IsConservative.killedSemigroup P hP U hU hFeller hK))
        times (Cemetery.alive x) := by
  induction n generalizing x with
  | zero =>
      rw [finiteTimeKernel_zero, Kernel.const_apply]
      have hconst : (fun omega : LifetimePath U ↦
          fun i : Fin 0 ↦ LifetimePath.coordinate (times i) omega) =
          fun _ ↦ FiniteOrderedTimes.emptyPath (Cemetery U) := by
        funext omega
        exact Subsingleton.elim _ _
      rw [hconst, Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
      have hmeasTimes : Measurable (fun omega : ContinuousPath alpha ↦ fun i : Fin (n + 1) ↦
            LifetimePath.coordinate (times i) (ContinuousPath.killAtExit U omega)) :=
        Measurable.of_eval fun i ↦
          ContinuousPath.measurable_coordinate_killAtExit U hU (times i)
      have hmeasTail : Measurable (fun omega : ContinuousPath alpha ↦ fun i : Fin n ↦
              LifetimePath.coordinate (times.relativeTail i)
                (ContinuousPath.killAtExit U omega)) :=
        Measurable.of_eval fun i ↦
          ContinuousPath.measurable_coordinate_killAtExit U hU (times.relativeTail i)
      have hRcons : (cemeterySemigroup (IsConservative.killedSemigroup P hP U hU hFeller
          hK)).IsConservative := isConservative_cemeterySemigroup _
      let : IsMarkovKernel (finiteTimeKernel (cemeterySemigroup (IsConservative.killedSemigroup
          P hP U hU hFeller hK)) times) :=
        hRcons.isMarkovKernel_finiteTimeKernel _ times
      let : IsMarkovKernel (finiteTimeKernel (cemeterySemigroup (IsConservative.killedSemigroup
          P hP U hU hFeller hK)) times.relativeTail) :=
        hRcons.isMarkovKernel_finiteTimeKernel _ _
      let : IsMarkovKernel ((cemeterySemigroup (IsConservative.killedSemigroup P hP U hU hFeller
          hK)) (times 0)) := hRcons.isMarkovKernel (times 0)
      rw [IsConservative.killedProcess_map_coordinates P hP U hU _ x]
      have : IsProbabilityMeasure
          ((IsConservative.continuousProcess P hP (x : alpha)).map (fun omega : ContinuousPath
              alpha ↦ fun i : Fin (n + 1) ↦
            LifetimePath.coordinate (times i) (ContinuousPath.killAtExit U omega))) :=
        inferInstance
      refine MeasureTheory.ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi ?_ ?_
      · rintro _ ⟨B, hB, rfl⟩
        have hBmeas : ∀ i : Fin (n + 1), MeasurableSet (B i) := fun i ↦ hB i (Set.mem_univ i)
        have hbox : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hBmeas
        have hbox' : MeasurableSet (Set.univ.pi fun i : Fin n ↦ B i.succ) :=
          MeasurableSet.univ_pi fun i ↦ hBmeas i.succ
        have hC0 : MeasurableSet (Cemetery.alive ⁻¹' (B 0) : Set U) := measurable_inl (hBmeas 0)
        have hA : MeasurableSet {omega : ContinuousPath alpha |
            ((times 0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} :=
          ContinuousPath.measurableSet_lt_exitTime U hU (times 0)
        have hg : Measurable fun z : Cemetery U ↦
            finiteTimeKernel (cemeterySemigroup (IsConservative.killedSemigroup P hP U hU
                hFeller hK)) times.relativeTail z (Set.univ.pi fun i : Fin n ↦ B i.succ) :=
          (finiteTimeKernel (cemeterySemigroup (IsConservative.killedSemigroup P hP U hU hFeller
              hK)) times.relativeTail).measurable_coe hbox'
        have hinl : Measurable (Cemetery.alive : U → Cemetery U) := measurable_inl
        have hcoorddead : ∀ omega : ContinuousPath alpha,
            omega ∉ {omega : ContinuousPath alpha |
            ((times 0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} →
            ∀ i : Fin (n + 1), LifetimePath.coordinate (times i)
              (ContinuousPath.killAtExit U omega) = Cemetery.delta := fun omega homega i ↦
          ContinuousPath.coordinate_killAtExit_of_exitTime_le U omega
            (not_lt.mp homega) (times.monotone (Fin.zero_le i))
        have hliveset := killed_coordinate_survival_event U times B
        have hliveval : IsConservative.continuousProcess P hP (x : alpha)
            ((fun omega : ContinuousPath alpha ↦ fun i : Fin (n + 1) ↦
            LifetimePath.coordinate (times i) (ContinuousPath.killAtExit U omega)) ⁻¹'
                Set.univ.pi B ∩ {omega : ContinuousPath alpha |
            ((times 0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}) =
            ∫⁻ y in (Cemetery.alive ⁻¹' (B 0) : Set U), finiteTimeKernel (cemeterySemigroup
                (IsConservative.killedSemigroup P hP U hU hFeller hK)) times.relativeTail
              (Cemetery.alive y) (Set.univ.pi fun i : Fin n ↦ B i.succ)
                  ∂(IsConservative.killedKernelOn P hP U hU (times 0) x) := by
          rw [hliveset, IsConservative.continuousProcess_killedEvent_inter_shift P hP U hU
            hFeller hK (times 0) x hC0 (hmeasTail hbox')]
          refine lintegral_congr fun y ↦ ?_
          rw [← Measure.map_apply hmeasTail hbox',
            ← IsConservative.killedProcess_map_coordinates P hP U hU _ y,
            ih times.relativeTail y]
        have hdeadval : IsConservative.continuousProcess P hP (x : alpha)
            ((fun omega : ContinuousPath alpha ↦ fun i : Fin (n + 1) ↦
            LifetimePath.coordinate (times i) (ContinuousPath.killAtExit U omega)) ⁻¹'
                Set.univ.pi B \ {omega : ContinuousPath alpha |
            ((times 0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega}) =
            (1 - IsConservative.killedKernelOn P hP U hU (times 0) x Set.univ) *
              (B 0).indicator (fun z ↦ finiteTimeKernel (cemeterySemigroup
                  (IsConservative.killedSemigroup P hP U hU hFeller hK)) times.relativeTail z
                (Set.univ.pi fun i : Fin n ↦ B i.succ)) Cemetery.delta := by
          have hQA : IsConservative.continuousProcess P hP (x : alpha) ({omega : ContinuousPath
              alpha |
            ((times 0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega})ᶜ =
              1 - IsConservative.killedKernelOn P hP U hU (times 0) x Set.univ := by
            rw [IsConservative.killedKernelOn_univ_eq_continuousProcess P hP U hU (times 0) x]
            exact prob_compl_eq_one_sub hA
          by_cases hdelta : ∀ i : Fin (n + 1), (Cemetery.delta : Cemetery U) ∈ B i
          · have hset : (fun omega : ContinuousPath alpha ↦ fun i : Fin (n + 1) ↦
            LifetimePath.coordinate (times i) (ContinuousPath.killAtExit U omega)) ⁻¹'
                Set.univ.pi B \ {omega : ContinuousPath alpha |
            ((times 0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} = ({omega :
                ContinuousPath alpha |
            ((times 0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega})ᶜ := by
              refine Set.eq_of_subset_of_subset (fun omega homega ↦ homega.2) fun omega homega ↦ ?_
              refine ⟨fun i _ ↦ ?_, homega⟩
              have hci : LifetimePath.coordinate (times i)
                  (ContinuousPath.killAtExit U omega) ∈ B i := by
                rw [hcoorddead omega homega i]
                exact hdelta i
              exact hci
            rw [hset, hQA, Set.indicator_of_mem (hdelta 0),
              finiteTimeKernel_cemeterySemigroup_delta, Measure.dirac_apply' _ hbox',
              Set.indicator_of_mem
                (show (fun _ ↦ Cemetery.delta : Fin n → Cemetery U) ∈
                  (Set.univ.pi fun i : Fin n ↦ B i.succ) from fun i _ ↦ hdelta i.succ),
              Pi.one_apply, mul_one]
          · obtain ⟨i, hi⟩ := not_forall.mp hdelta
            have hset : (fun omega : ContinuousPath alpha ↦ fun i : Fin (n + 1) ↦
            LifetimePath.coordinate (times i) (ContinuousPath.killAtExit U omega)) ⁻¹'
                Set.univ.pi B \ {omega : ContinuousPath alpha |
            ((times 0 : NNReal) : ℝ≥0∞) < ContinuousPath.exitTime U omega} = ∅ := by
              refine Set.eq_empty_iff_forall_notMem.mpr fun omega homega ↦ ?_
              have h1 : LifetimePath.coordinate (times i)
                  (ContinuousPath.killAtExit U omega) ∈ B i := homega.1 i (Set.mem_univ i)
              rw [hcoorddead omega homega.2 i] at h1
              exact hi h1
            rw [hset, measure_empty]
            by_cases h0 : (Cemetery.delta : Cemetery U) ∈ B 0
            · have hnotbox : (fun _ ↦ Cemetery.delta : Fin n → Cemetery U) ∉ (Set.univ.pi fun i
                : Fin n ↦ B i.succ) := by
                intro hmem
                exact hdelta fun k ↦ Fin.cases h0 (fun j ↦ hmem j (Set.mem_univ j)) k
              rw [Set.indicator_of_mem h0, finiteTimeKernel_cemeterySemigroup_delta,
                Measure.dirac_apply' _ hbox', Set.indicator_of_notMem hnotbox, mul_zero]
            · rw [Set.indicator_of_notMem h0, mul_zero]
        have hintegrand : ∀ z : Cemetery U,
            finiteTimeKernel (cemeterySemigroup (IsConservative.killedSemigroup P hP U hU
                hFeller hK)) times.relativeTail z
              (Prod.mk z ⁻¹' ((fun w : Cemetery U × (Fin n → Cemetery U) ↦
                @Fin.cons n (fun _ : Fin (n + 1) ↦ Cemetery U) w.1 w.2) ⁻¹' Set.univ.pi B)) =
            (B 0).indicator (fun z ↦ finiteTimeKernel (cemeterySemigroup
                (IsConservative.killedSemigroup P hP U hU hFeller hK)) times.relativeTail z
              (Set.univ.pi fun i : Fin n ↦ B i.succ)) z := by
          intro z
          by_cases hz : z ∈ B 0
          · rw [Set.indicator_of_mem hz]
            congr 1
            ext q
            simp only [Set.mem_preimage, Set.mem_univ_pi]
            constructor
            · intro h j
              have hj := h j.succ
              rwa [Fin.cons_succ] at hj
            · intro h j
              refine Fin.cases ?_ (fun k ↦ ?_) j
              · rw [Fin.cons_zero]
                exact hz
              · rw [Fin.cons_succ]
                exact h k
          · rw [Set.indicator_of_notMem hz]
            have hempty : (Prod.mk z ⁻¹' ((fun w : Cemetery U × (Fin n → Cemetery U) ↦
                @Fin.cons n (fun _ : Fin (n + 1) ↦ Cemetery U) w.1 w.2) ⁻¹'
                  Set.univ.pi B)) = ∅ := by
              refine Set.eq_empty_iff_forall_notMem.mpr fun q hq ↦ ?_
              have h0 : @Fin.cons n (fun _ : Fin (n + 1) ↦ Cemetery U) z q 0 ∈ B 0 :=
                hq 0 (Set.mem_univ 0)
              rw [Fin.cons_zero] at h0
              exact hz h0
            rw [hempty, measure_empty]
        rw [Measure.map_apply hmeasTimes hbox,
          ← measure_inter_add_sdiff (μ := IsConservative.continuousProcess P hP (x : alpha))
            ((fun omega : ContinuousPath alpha ↦ fun i : Fin (n + 1) ↦
            LifetimePath.coordinate (times i) (ContinuousPath.killAtExit U omega)) ⁻¹'
                Set.univ.pi B) hA,
          hliveval, hdeadval, finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
          Kernel.map_apply _ measurable_finCons, Measure.map_apply measurable_finCons hbox,
          Kernel.compProd_apply (measurable_finCons hbox)]
        simp only [Kernel.prodMkLeft_apply]
        rw [lintegral_congr hintegrand, lintegral_indicator (hBmeas 0), cemeterySemigroup_apply,
          IsConservative.killedSemigroup_apply, Kernel.cemeteryExtension_alive_apply,
          Measure.restrict_add, lintegral_add_measure,
          setLIntegral_map (hBmeas 0) hg hinl, Measure.restrict_smul, lintegral_smul_measure,
          ← lintegral_indicator (hBmeas 0), lintegral_dirac' _ (hg.indicator (hBmeas 0)),
          smul_eq_mul]
      · rw [measure_univ, measure_univ]

/-- **The finite-dimensional distributions of the killed process.**  For every finite set `I` of
nonnegative times and every starting point `x` of the open set `U`, the coordinates at `I` of the
process killed at the exit of `U` have the law of the finite-set kernel at `I` of the cemetery
extension of the killed semigroup on `U`, started at the live state `x`.

This identifies the process killed at the exit of `U` with the process of the killed semigroup,
the cemetery recording the time at which the path leaves `U`. -/
theorem IsConservative.killedProcess_map_finiteEvaluation (I : Finset NNReal) (x : U) :
    (IsConservative.killedProcess P hP U hU x).map
        (fun omega ↦ fun i : I ↦ LifetimePath.coordinate (i : NNReal) omega) =
      finiteSetKernel (cemeterySemigroup (IsConservative.killedSemigroup P hP U hU hFeller hK))
          I (Cemetery.alive x) := by
  have hfun : orderedPathToFiniteSet (α := Cemetery U) I ∘
      (fun omega : LifetimePath U ↦ fun j : Fin I.card ↦
        LifetimePath.coordinate (finiteSetTimes I j) omega) =
      fun omega : LifetimePath U ↦ fun t : I ↦ LifetimePath.coordinate (t : NNReal) omega := by
    funext omega t
    change LifetimePath.coordinate (finiteSetTimes I ((I.orderIsoOfFin rfl).symm t)) omega =
      LifetimePath.coordinate (t : NNReal) omega
    rw [finiteSetTimes_orderIsoOfFin_symm_apply]
  rw [finiteSetKernel_eq_map, Kernel.map_apply _ (measurable_orderedPathToFiniteSet I),
    ← IsConservative.killedProcess_map_coordinates_ordered P hP U hU hFeller hK
      (finiteSetTimes I) x,
    Measure.map_map (measurable_orderedPathToFiniteSet I)
      (LifetimePath.measurable_coordinateFamily _), hfun]

end OrderedMarginals

end SubMarkovKernelSemigroup

end MarkovProcess
