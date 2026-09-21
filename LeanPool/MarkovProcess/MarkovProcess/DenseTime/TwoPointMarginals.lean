/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.DenseTime.TrajectoryMarginals
import LeanPool.MarkovProcess.MarkovProcess.Kernel.KolmogorovMoments
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Process.Kolmogorov

/-!
# Two-point marginals of the dense-time trajectory, and the intrinsic Kolmogorov bridge

The dense-time trajectory of a conservative sub-Markov kernel semigroup already has identified
one-time marginals.  This file identifies its two-time marginals: at dense times whose physical
images satisfy `iota d < iota d'`, the pair `(path d, path d')` has the law obtained by running
`P` for time `iota d` and then, from the state reached, for the increment `iota d' - iota d`.

The identification is then used to discharge the coordinate Kolmogorov hypothesis that every
trajectory theorem of the library assumes.  Under the intrinsic semigroup bound
`SubMarkovKernelSemigroup.HasKolmogorovMoments`, the canonical dense-time coordinate process is a
Kolmogorov process with a positive Hölder exponent below `(q - 1) / p`.

No continuity, modification, Markov-property, or path-regularity statement is proved here; only
the two-point law and the moment estimate it transports.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

section

namespace DenseTime

/-- On dense time the extended distance between ordered times is the physical time increment. -/
theorem edist_eq_castOrderEmbedding_sub {s t : DenseTime} (hst : s ≤ t) :
    edist s t = ((castOrderEmbedding t - castOrderEmbedding s : ℝ≥0) : ℝ≥0∞) := by
  have hcast : castOrderEmbedding s ≤ castOrderEmbedding t :=
    castOrderEmbedding.monotone hst
  have hcoe : ∀ r : DenseTime, ((castOrderEmbedding r : ℝ≥0) : ℝ) = ((r : ℚ) : ℝ) := by
    intro r
    simp only [castOrderEmbedding, NNRat.castOrderEmbedding_apply]
    push_cast
    rfl
  have hreal : ((s : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ) := by
    rw [← hcoe s, ← hcoe t]
    exact_mod_cast hcast
  rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_sub hcast, NNRat.dist_eq, ← Rat.dist_cast, Real.dist_eq, hcoe, hcoe,
    abs_sub_comm, abs_of_nonneg (by linarith only [hreal])]

/-- The physical embedding of dense time is an isometry for the extended distance. -/
theorem dist_castOrderEmbedding (r r' : DenseTime) :
    dist (castOrderEmbedding r) (castOrderEmbedding r') = dist r r' := by
  have hcoe : ∀ u : DenseTime, ((castOrderEmbedding u : ℝ≥0) : ℝ) = ((u : ℚ) : ℝ) := by
    intro u
    simp only [castOrderEmbedding, NNRat.castOrderEmbedding_apply]
    push_cast
    rfl
  rw [NNReal.dist_eq, hcoe, hcoe, NNRat.dist_eq, ← Rat.dist_cast, Real.dist_eq]

/-- The physical embedding of dense time preserves the extended distance. -/
theorem edist_castOrderEmbedding (r r' : DenseTime) :
    edist (castOrderEmbedding r) (castOrderEmbedding r') = edist r r' := by
  rw [edist_dist, edist_dist, dist_castOrderEmbedding]

end DenseTime

namespace SubMarkovKernelSemigroup

section CompProd

variable {A B C E : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace E]

/-- A composition-product whose second factor ignores the starting point is the measure-level
composition-product of the first factor's law with that second factor. -/
private theorem compProd_prodMkLeft_apply (kappa : Kernel A B) [IsSFiniteKernel kappa]
    (eta : Kernel B C) [IsSFiniteKernel eta] (x : A) :
    (kappa ⊗ₖ Kernel.prodMkLeft A eta) x = (kappa x) ⊗ₘ eta := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  simp only [Kernel.prodMkLeft_apply]

/-- Pushing the second coordinate of such a composition-product forward along a measurable map
is the composition-product with the pushed-forward second factor. -/
private theorem compProd_prodMkLeft_map (kappa : Kernel A B) [IsSFiniteKernel kappa]
    (eta : Kernel B C) [IsSFiniteKernel eta] {g : C → E} (hg : Measurable g) :
    (kappa ⊗ₖ Kernel.prodMkLeft A eta).map (Prod.map id g) =
      kappa ⊗ₖ Kernel.prodMkLeft A (eta.map g) := by
  ext x
  rw [Kernel.map_apply _ (measurable_id.prodMap hg), compProd_prodMkLeft_apply,
    compProd_prodMkLeft_apply, Measure.compProd_map hg]

end CompProd

section TwoPoint

variable {D alpha : Type*} [MeasurableSpace alpha]

private theorem measurable_finConsOne :
    Measurable
      (fun z : alpha × (Fin 1 → alpha) ↦ @Fin.cons 1 (fun _ : Fin 2 ↦ alpha) z.1 z.2) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using
      (measurable_fst : Measurable (Prod.fst : alpha × (Fin 1 → alpha) → alpha))
  · simpa only [Fin.cons_succ] using!
      (measurable_pi_apply j).comp
        (measurable_snd : Measurable (Prod.snd : alpha × (Fin 1 → alpha) → _))

namespace IsConservative

/-- The two-coordinate finite-time kernel is the transition kernel at the first time followed by
the transition kernel over the increment to the second time. -/
theorem finiteTimeKernel_two_map_pair (P : SubMarkovKernelSemigroup alpha)
    (hP : P.IsConservative) (u : FiniteOrderedTimes 2) :
    (finiteTimeKernel P u).map (fun path ↦ (path 0, path 1)) =
      P (u 0) ⊗ₖ Kernel.prodMkLeft alpha (P (u 1 - u 0)) := by
  let : IsFiniteKernel (P (u 0)) := (P.isSubMarkovKernel (u 0)).isFiniteKernel
  let : IsFiniteKernel (P (u.relativeTail 0)) :=
    (P.isSubMarkovKernel (u.relativeTail 0)).isFiniteKernel
  let : IsMarkovKernel (finiteTimeKernel P u.relativeTail) :=
    hP.isMarkovKernel_finiteTimeKernel P u.relativeTail
  have hmeasPair : Measurable (fun path : Fin 2 → alpha ↦ (path 0, path 1)) := by fun_prop
  have hcomp :
      (fun path : Fin 2 → alpha ↦ (path 0, path 1)) ∘
          (fun z : alpha × (Fin 1 → alpha) ↦ @Fin.cons 1 (fun _ : Fin 2 ↦ alpha) z.1 z.2) =
        Prod.map id (fun path : Fin 1 → alpha ↦ path 0) := by
    funext z
    rfl
  have htail : u.relativeTail 0 = u 1 - u 0 := rfl
  rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
    ← Kernel.map_comp_right _ measurable_finConsOne hmeasPair, hcomp,
    compProd_prodMkLeft_map _ _ (measurable_pi_apply (0 : Fin 1)),
    finiteTimeKernel_one_map_eval, htail]

variable [StandardBorelSpace alpha] [Nonempty alpha]

private theorem denseTimeTrajectory_map_pair_aux
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) {n : ℕ} (k l : ℕ) (hk : k < n) (hl : l < n)
    (hlt : iota (e k) < iota (e l)) :
    (denseTimeTrajectory P hP e iota).map (fun path ↦ (path (e k), path (e l))) =
      P (iota (e k)) ⊗ₖ Kernel.prodMkLeft alpha (P (iota (e l) - iota (e k))) := by
  classical
  set i : Fin n := ⟨k, hk⟩ with hi
  set j : Fin n := ⟨l, hl⟩ with hj
  have hpair : Measurable (fun path : Fin n → alpha ↦ (path i, path j)) := by fun_prop
  have hstep1 :
      (fun path : Fin n → alpha ↦ (path i, path j)) ∘ denseTimeTrajectoryPrefix e n =
        fun path : D → alpha ↦ (path (e k), path (e l)) := rfl
  rw [← hstep1, Kernel.map_comp_right _ (measurable_denseTimeTrajectoryPrefix e n) hpair,
    denseTimeTrajectory_map_prefix P hP e iota n, denseTimePrefixKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_denseTimePrefixReindex e iota n) hpair]
  set J : Finset NNReal := denseTimePhysicalPrefix e iota n with hJ
  have hmem : ∀ m : Fin n, iota (e (m : ℕ)) ∈ J := by
    intro m
    rw [hJ, denseTimePhysicalPrefix, Finset.mem_map]
    refine ⟨e (m : ℕ), ?_, rfl⟩
    rw [CountableEnumeration.mem_prefix_iff, e.symm_apply_apply]
    exact m.isLt
  have hstep2 :
      (fun path : Fin n → alpha ↦ (path i, path j)) ∘ denseTimePrefixReindex e iota n =
        fun path : J → alpha ↦
          (path ⟨iota (e (i : ℕ)), hmem i⟩, path ⟨iota (e (j : ℕ)), hmem j⟩) := rfl
  have hpairJ : Measurable (fun path : J → alpha ↦
      (path ⟨iota (e (i : ℕ)), hmem i⟩, path ⟨iota (e (j : ℕ)), hmem j⟩)) := by fun_prop
  rw [hstep2, finiteSetKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet J) hpairJ]
  set a : Fin J.card := (J.orderIsoOfFin rfl).symm ⟨iota (e (i : ℕ)), hmem i⟩ with ha
  set b : Fin J.card := (J.orderIsoOfFin rfl).symm ⟨iota (e (j : ℕ)), hmem j⟩ with hb
  have hstep3 :
      (fun path : J → alpha ↦
          (path ⟨iota (e (i : ℕ)), hmem i⟩, path ⟨iota (e (j : ℕ)), hmem j⟩)) ∘
            orderedPathToFiniteSet J =
        fun path : Fin J.card → alpha ↦ (path a, path b) := rfl
  rw [hstep3]
  have hab : a < b := by
    rw [ha, hb, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]
    exact hlt
  set select : Fin 2 ↪o Fin J.card :=
    OrderEmbedding.ofStrictMono (fun m ↦ if m = 0 then a else b) (by
      rw [Fin.strictMono_iff_lt_succ]
      intro m
      have hm : m = 0 := Subsingleton.elim m 0
      subst hm
      simpa only [Fin.castSucc_zero, ite_eq_left rfl, Fin.succ_zero_eq_one] using! hab) with hselect
  have hpair2 : Measurable (fun path : Fin 2 → alpha ↦ (path 0, path 1)) := by fun_prop
  have hstep4 :
      (fun path : Fin 2 → alpha ↦ (path 0, path 1)) ∘
          FiniteOrderedTimes.restrictPath select =
        fun path : Fin J.card → alpha ↦ (path a, path b) := rfl
  rw [← hstep4,
    Kernel.map_comp_right _ (FiniteOrderedTimes.measurable_restrictPath select) hpair2,
    hP.finiteTimeKernel_map_restrictPath P (finiteSetTimes J) select,
    finiteTimeKernel_two_map_pair P hP]
  have hta : ((finiteSetTimes J).restrict select) 0 = iota (e k) := by
    change ((((J.orderIsoOfFin rfl) a) : J) : NNReal) = iota (e k)
    rw [ha, OrderIso.apply_symm_apply]
  have htb : ((finiteSetTimes J).restrict select) 1 = iota (e l) := by
    change ((((J.orderIsoOfFin rfl) b) : J) : NNReal) = iota (e l)
    rw [hb, OrderIso.apply_symm_apply]
  rw [hta, htb]

/-- The two-time marginal of the dense-time trajectory: at dense labels whose physical times are
strictly ordered, the pair of coordinates has the law of `P` run for the first physical time and
then, from the state reached, for the increment to the second physical time. -/
theorem denseTimeTrajectory_map_pair
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) {d d' : D} (hlt : iota d < iota d') :
    (denseTimeTrajectory P hP e iota).map (fun path ↦ (path d, path d')) =
      P (iota d) ⊗ₖ Kernel.prodMkLeft alpha (P (iota d' - iota d)) := by
  have hd : e (e.symm d) = d := e.apply_symm_apply d
  have hd' : e (e.symm d') = d' := e.apply_symm_apply d'
  have hpair := denseTimeTrajectory_map_pair_aux P hP e iota
    (n := max (e.symm d) (e.symm d') + 1) (e.symm d) (e.symm d')
    (Nat.lt_succ_of_le (le_max_left _ _)) (Nat.lt_succ_of_le (le_max_right _ _))
    (by rw [hd, hd']; exact hlt)
  rwa [hd, hd'] at hpair

end IsConservative

end TwoPoint

section Bridge

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [StandardBorelSpace alpha] [Nonempty alpha]

namespace IsConservative

private theorem lintegral_edist_le_of_lt
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (x : alpha)
    {s t : DenseTime} (hst : s < t) :
    ∫⁻ omega, edist (omega s) (omega t) ^ p
        ∂(denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) ≤ M * edist s t ^ q := by
  set iota : DenseTime ↪ NNReal := DenseTime.castOrderEmbedding.toEmbedding with hiota
  have hlt : iota s < iota t := DenseTime.castOrderEmbedding.strictMono hst
  set Delta : NNReal := iota t - iota s with hDelta
  let : IsFiniteKernel (P (iota s)) := (P.isSubMarkovKernel (iota s)).isFiniteKernel
  let : IsFiniteKernel (P Delta) := (P.isSubMarkovKernel Delta).isFiniteKernel
  have hF : Measurable (fun z : alpha × alpha ↦ edist z.1 z.2 ^ p) :=
    measurable_edist.pow_const p
  have hev : Measurable (fun omega : DenseTime → alpha ↦ (omega s, omega t)) := by fun_prop
  have hmapint :
      ∫⁻ z, edist z.1 z.2 ^ p
          ∂((denseTimeTrajectory P hP DenseTime.enumeration iota x).map
            (fun omega ↦ (omega s, omega t))) =
        ∫⁻ omega, edist (omega s) (omega t) ^ p
          ∂(denseTimeTrajectory P hP DenseTime.enumeration iota x) :=
    lintegral_map hF hev
  have hlaw :
      (denseTimeTrajectory P hP DenseTime.enumeration iota x).map
          (fun omega ↦ (omega s, omega t)) = (P (iota s) x) ⊗ₘ P Delta := by
    rw [← Kernel.map_apply _ hev,
      denseTimeTrajectory_map_pair P hP DenseTime.enumeration iota hlt,
      compProd_prodMkLeft_apply]
  have hinner : ∀ y : alpha,
      ∫⁻ z, edist y z ^ p ∂(P Delta y) ≤ (M : ℝ≥0∞) * (Delta : ℝ≥0∞) ^ q := by
    intro y
    have hcongr : ∫⁻ z, edist y z ^ p ∂(P Delta y) = ∫⁻ z, edist z y ^ p ∂(P Delta y) :=
      lintegral_congr fun z ↦ by rw [edist_comm]
    rw [hcongr]
    exact hmom.lintegral_edist_le Delta y
  rw [← hmapint, hlaw, Measure.lintegral_compProd hF]
  calc ∫⁻ y, ∫⁻ z, edist y z ^ p ∂(P Delta y) ∂(P (iota s) x)
      ≤ ∫⁻ _, (M : ℝ≥0∞) * (Delta : ℝ≥0∞) ^ q ∂(P (iota s) x) := lintegral_mono hinner
    _ = (M : ℝ≥0∞) * (Delta : ℝ≥0∞) ^ q := by
        rw [lintegral_const, hP (iota s) x, mul_one]
    _ = (M : ℝ≥0∞) * edist s t ^ q := by
        rw [DenseTime.edist_eq_castOrderEmbedding_sub hst.le]
        rfl

/-- **The dense-time coordinate process is a Kolmogorov process, with the semigroup's own
constants.**  Under the intrinsic moment bound `HasKolmogorovMoments p q M`, the canonical
dense-time coordinate process of `P` started from any state satisfies the Kolmogorov increment
condition with exactly the exponents `p`, `q` and the constant `M` of that bound.  In particular
the estimate is uniform in the starting state. -/
theorem isKolmogorovProcess_denseTimeTrajectory
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (x : alpha) :
    IsKolmogorovProcess (fun r omega ↦ omega r)
      (denseTimeTrajectory P hP DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding x) p q M := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun r ↦ measurable_pi_apply r) ?_ hmom.p_pos hmom.q_pos
  intro s t
  rcases lt_trichotomy s t with hst | hst | hst
  · exact lintegral_edist_le_of_lt P hP hmom x hst
  · subst hst
    simp only [edist_self, ENNReal.zero_rpow_of_pos hmom.p_pos, lintegral_zero]
    exact zero_le
  · have hsym := lintegral_edist_le_of_lt P hP hmom x hst
    have hcongr :
        ∫⁻ omega, edist (omega s) (omega t) ^ p
            ∂(denseTimeTrajectory P hP DenseTime.enumeration
              DenseTime.castOrderEmbedding.toEmbedding x) =
          ∫⁻ omega, edist (omega t) (omega s) ^ p
            ∂(denseTimeTrajectory P hP DenseTime.enumeration
              DenseTime.castOrderEmbedding.toEmbedding x) :=
      lintegral_congr fun omega ↦ by rw [edist_comm]
    rw [hcongr, edist_comm s t]
    exact hsym

/-- An intrinsic Kolmogorov moment bound on the semigroup implies the coordinate Kolmogorov
hypothesis assumed by every trajectory theorem of the library: for each starting state the
canonical dense-time coordinate process is a Kolmogorov process admitting a positive Hölder
exponent strictly below the Kolmogorov--Chentsov threshold. -/
theorem kolmogorovRegular_of_hasKolmogorovMoments
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) :
    ∀ x, ∃ p q gamma : ℝ, ∃ M : ℝ≥0,
      IsKolmogorovProcess (fun r omega ↦ omega r)
          (denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) p q M ∧
        0 < gamma ∧ gamma < (q - 1) / p := by
  intro x
  obtain ⟨gamma, hgamma0, hgammalt⟩ := hmom.exists_holderExponent
  exact ⟨p, q, gamma, M, isKolmogorovProcess_denseTimeTrajectory P hP hmom x, hgamma0, hgammalt⟩

end IsConservative

end Bridge

end SubMarkovKernelSemigroup

end

end MarkovProcess

end PortComputability
