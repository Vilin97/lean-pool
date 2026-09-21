/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.FiniteTime.KernelEquivariance
import LeanPool.MarkovProcess.MarkovProcess.Main

/-!
# Equivariance of the continuous-path process

Let `P` be a conservative Feller sub-Markov kernel semigroup on `alpha` with a Kolmogorov-regular
continuous-path process, let `e : alpha ≃ₜ beta` be a homeomorphism onto a second state space and
`c > 0` a time factor, and let `P'` be the rescaled conjugate of `P` on `beta`, that is
`P' t x = ((P (c * t)) (e.symm x)).map e`.  Then the continuous-path process of `P'` is the
continuous-path process of `P` started at `e.symm x` and pushed forward by the path map
`omega ↦ fun t ↦ e (omega (c * t))`.

The proof goes through the uniqueness theorem of `MarkovProcess/Main.lean`: the pushed-forward
kernel is a Markov kernel whose finite-dimensional distributions are computed from the Feller
marginal theorem for `P` at the rescaled times together with the finite-dimensional transfer
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteSetKernel_eq`.

Main results: `ContinuousPath.rescale` and its continuity and measurability;
`SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered`,
the marginal of the continuous-path process at an arbitrary strictly increasing finite family of
times; `SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale` and its
pointwise form `continuousProcess_apply_rescale`; the intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`, whose only regularity hypothesis is a
Kolmogorov moment bound on `P` when `e` is an isometry; and the two degenerate corollaries, pure
time rescaling (`continuousProcess_eq_map_timeRescale`) and pure conjugation
(`continuousProcess_eq_map_conjugate`).

No scaling limit is asserted: `c` is a fixed positive factor and both semigroups are given in
advance.  The two state spaces may coincide; the degenerate corollaries are stated on one space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

namespace ContinuousPath

section Rescale

variable {alpha beta gamma : Type*} [TopologicalSpace alpha] [TopologicalSpace beta]
  [TopologicalSpace gamma]

/-- Multiplication of nonnegative time by a fixed factor, as a continuous self-map of `NNReal`. -/
def timeScaling (c : NNReal) : C(NNReal, NNReal) where
  toFun t := c * t
  continuous_toFun := continuous_const.mul continuous_id

/-- Time scaling, evaluated. -/
@[simp]
theorem timeScaling_apply (c t : NNReal) : timeScaling c t = c * t := rfl

/-- Speed a continuous path up by the factor `c` and conjugate its state by the homeomorphism
`e`. -/
def rescale (e : alpha ≃ₜ beta) (c : NNReal) (omega : ContinuousPath alpha) :
    ContinuousPath beta :=
  (e : C(alpha, beta)).comp (omega.comp (timeScaling c))

/-- The rescaled path, evaluated: `e` applied to the path at the sped-up time. -/
@[simp]
theorem rescale_apply (e : alpha ≃ₜ beta) (c : NNReal) (omega : ContinuousPath alpha)
    (t : NNReal) : rescale e c omega t = e (omega (c * t)) :=
  rfl

/-- Rescaling by the identity homeomorphism and the factor one is the identity. -/
@[simp]
theorem rescale_refl_one (omega : ContinuousPath alpha) :
    rescale (Homeomorph.refl alpha) 1 omega = omega := by
  ext t
  simp only [rescale_apply, Homeomorph.refl_apply, id_eq, one_mul]

/-- Rescaling by the identity homeomorphism speeds the path up without touching the state. -/
@[simp]
theorem rescale_refl_apply (c : NNReal) (omega : ContinuousPath alpha) (t : NNReal) :
    rescale (Homeomorph.refl alpha) c omega t = omega (c * t) :=
  rfl

/-- Rescaling by the time factor one conjugates the state without touching the time. -/
@[simp]
theorem rescale_one_apply (e : alpha ≃ₜ beta) (omega : ContinuousPath alpha) (t : NNReal) :
    rescale e 1 omega t = e (omega t) := by
  simp only [rescale_apply, one_mul]

/-- Rescaling is jointly functorial in the homeomorphism and the time factor. -/
theorem rescale_rescale (e : beta ≃ₜ gamma) (d : alpha ≃ₜ beta) (c b : NNReal)
    (omega : ContinuousPath alpha) :
    rescale e c (rescale d b omega) = rescale (d.trans e) (b * c) omega := by
  ext t
  simp only [rescale_apply, Homeomorph.trans_apply, mul_assoc]

/-- Rescaling is continuous for the compact-open topology. -/
theorem continuous_rescale (e : alpha ≃ₜ beta) (c : NNReal) :
    Continuous (rescale e c : ContinuousPath alpha → ContinuousPath beta) :=
  (ContinuousMap.continuous_postcomp (e : C(alpha, beta))).comp
    (ContinuousMap.continuous_precomp (timeScaling c))

/-- Rescaling is Borel measurable on continuous-path space. -/
theorem measurable_rescale (e : alpha ≃ₜ beta) (c : NNReal) :
    Measurable (rescale e c : ContinuousPath alpha → ContinuousPath beta) :=
  (continuous_rescale e c).measurable

/-- Reading a rescaled path at a finite set of times reads the original path at the sped-up
times and conjugates the states. -/
theorem finsetEvaluation_rescale (e : alpha ≃ₜ beta) (c : NNReal) (I : Finset NNReal)
    (omega : ContinuousPath alpha) :
    finsetEvaluation I (rescale e c omega) = fun t : I ↦ e (omega (c * (t : NNReal))) :=
  rfl

end Rescale

end ContinuousPath

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **Marginals at arbitrary ordered times.**  The law of the continuous-path process of a
conservative Feller semigroup, read at a strictly increasing finite family of nonnegative times,
is the finite-time kernel of `P` at those times.  This is the finite-set marginal theorem of
`MarkovProcess/Main.lean` transported to an arbitrary strictly increasing indexing. -/
theorem IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) {n : ℕ}
    (times : FiniteOrderedTimes n) :
    (continuousProcess P hP).map (ContinuousPath.finiteEvaluation (fun i ↦ times i)) =
      finiteTimeKernel P times := by
  classical
  have hmem : ∀ i : Fin n,
      times i ∈ Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n)) :=
    fun i ↦ Finset.mem_image_of_mem _ (Finset.mem_univ i)
  let I : Finset NNReal := Finset.image (fun j ↦ times j) (Finset.univ : Finset (Fin n))
  let phi : Fin n ↪o I :=
    OrderEmbedding.ofStrictMono (fun i ↦ (⟨times i, hmem i⟩ : I))
      (fun _ _ hij ↦ times.strictMono hij)
  let emb : Fin n ↪o Fin I.card := phi.trans (I.orderIsoOfFin rfl).symm.toOrderEmbedding
  have hphi : ∀ i : Fin n, ((phi i : I) : NNReal) = times i := fun _ ↦ rfl
  have hsel : Measurable (fun w : I → alpha ↦ w ∘ (phi : Fin n → I)) :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (phi i)
  have hfinset : Measurable (ContinuousPath.finsetEvaluation (alpha := alpha) I) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finiteEvaluation (α := alpha) (fun i ↦ times i) =
      (fun w : I → alpha ↦ w ∘ (phi : Fin n → I)) ∘
        ContinuousPath.finsetEvaluation (alpha := alpha) I := rfl
  have hrestrict : (fun w : I → alpha ↦ w ∘ (phi : Fin n → I)) ∘
      orderedPathToFiniteSet (α := alpha) I = FiniteOrderedTimes.restrictPath emb := rfl
  have htimes : (finiteSetTimes I).restrict emb = times := by
    apply DFunLike.ext _ _
    intro i
    show finiteSetTimes I ((I.orderIsoOfFin rfl).symm (phi i)) = times i
    rw [finiteSetTimes_orderIsoOfFin_symm_apply, hphi i]
  rw [hcomp, Kernel.map_comp_right _ hfinset hsel,
    hFeller.continuousProcess_map_finiteEvaluation P hP hK I, finiteSetKernel_eq_map,
    ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet I) hsel, hrestrict,
    hP.finiteTimeKernel_map_restrictPath P (finiteSetTimes I) emb, htimes]

section TwoSpaces

variable {beta : Type*} [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P' : SubMarkovKernelSemigroup beta) (hP' : P'.IsConservative)

/-- **Equivariance of the continuous-path process.**  If `P'` is the rescaled conjugate of a
conservative Feller semigroup `P` by the homeomorphism `e` and the positive time factor `c`, then
the continuous-path process of `P'` is the continuous-path process of `P`, started at the
`e`-preimage of the initial state and pushed forward by the path map `ContinuousPath.rescale e c`.

The Feller hypothesis is needed only for `P`, because only the marginals of `P` at arbitrary real
times are used; `P'` enters through its Kolmogorov regularity alone. -/
theorem IsConservative.continuousProcess_eq_map_rescale
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hK' : P'.KolmogorovRegular hP') {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' e c) :
    continuousProcess P' hP' =
      (Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e c) := by
  classical
  let : IsMarkovKernel
      ((Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e c)) :=
    Kernel.IsMarkovKernel.map _ (ContinuousPath.measurable_rescale e c)
  refine (IsConservative.eq_continuousProcess_of_map_finiteEvaluation P' hP' hK' _ ?_).symm
  intro I
  have hmapPath : Measurable
      ((FiniteOrderedTimes.mapPath e : (I → alpha) → I → beta) ∘
        orderedPathToFiniteSet (α := alpha) I) :=
    (FiniteOrderedTimes.measurable_mapPath e.measurable).comp
      (measurable_orderedPathToFiniteSet I)
  have hfinite : Measurable (ContinuousPath.finiteEvaluation (α := alpha)
      (fun i ↦ ((finiteSetTimes I).rescale c hc) i)) :=
    ContinuousPath.measurable_finiteEvaluation _
  have hcomp : ContinuousPath.finsetEvaluation (alpha := beta) I ∘
        ContinuousPath.rescale e c =
      ((FiniteOrderedTimes.mapPath e : (I → alpha) → I → beta) ∘
        orderedPathToFiniteSet (α := alpha) I) ∘
        ContinuousPath.finiteEvaluation (α := alpha)
          (fun i ↦ ((finiteSetTimes I).rescale c hc) i) := by
    funext omega t
    show e (omega (c * (t : NNReal))) =
      e (omega (c * finiteSetTimes I ((I.orderIsoOfFin rfl).symm t)))
    rw [finiteSetTimes_orderIsoOfFin_symm_apply]
  rw [← Kernel.map_comp_right _ (ContinuousPath.measurable_rescale e c)
      (ContinuousPath.measurable_finiteEvaluation (fun t : I ↦ (t : NNReal))), hcomp,
    Kernel.map_comp_right _ hfinite hmapPath,
    ← Kernel.comap_map_comm _ e.symm.measurable hfinite,
    IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered P hP hFeller hK
      ((finiteSetTimes I).rescale c hc),
    IsRescaledConjugate.finiteSetKernel_eq h hc hP I]

/-- The equivariance identity at a fixed starting state: the law of the process of `P'` started at
`x` is the law of the process of `P` started at `e.symm x`, pushed forward by the rescaling map. -/
theorem IsConservative.continuousProcess_apply_rescale
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hK' : P'.KolmogorovRegular hP') {e : alpha ≃ₜ beta} {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' e c) (x : beta) :
    continuousProcess P' hP' x =
      ((continuousProcess P hP) (e.symm x)).map (ContinuousPath.rescale e c) := by
  rw [IsConservative.continuousProcess_eq_map_rescale P hP P' hP' hFeller hK hK' hc h,
    Kernel.map_apply _ (ContinuousPath.measurable_rescale e c), Kernel.comap_apply]

/-- **Intrinsic form of the equivariance theorem.**  When the state map is an isometry, the
Kolmogorov moment criterion for `P` alone gives the regularity of both processes, by
`IsRescaledConjugate.hasKolmogorovMoments`; no hypothesis on `P'` beyond conservativity and the
intertwining is then needed. -/
theorem IsConservative.continuousProcess_eq_map_rescale_of_hasKolmogorovMoments
    (hFeller : P.IsFellerKernelSemigroup) {p q : ℝ} {M : ℝ≥0}
    (hmom : P.HasKolmogorovMoments p q M) {e : alpha ≃ₜ beta}
    (he : Isometry (e : alpha → beta)) {c : NNReal} (hc : 0 < c)
    (h : IsRescaledConjugate P P' e c) :
    continuousProcess P' hP' =
      (Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e c) :=
  IsConservative.continuousProcess_eq_map_rescale P hP P' hP' hFeller
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom)
    (KolmogorovRegular.of_hasKolmogorovMoments P' hP' (h.hasKolmogorovMoments he hmom)) hc h

end TwoSpaces

section OneSpace

variable (P' : SubMarkovKernelSemigroup alpha) (hP' : P'.IsConservative)

/-- **Pure time rescaling.**  If the transition kernels of `P'` are those of `P` at the sped-up
times, then the continuous-path process of `P'` is the continuous-path process of `P` pushed
forward by the time change `omega ↦ fun t ↦ omega (c * t)`.  No state map is involved, so no
starting point has to be relabelled. -/
theorem IsConservative.continuousProcess_eq_map_timeRescale
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hK' : P'.KolmogorovRegular hP') {c : NNReal} (hc : 0 < c)
    (htime : ∀ t, P' t = P (c * t)) :
    continuousProcess P' hP' =
      (continuousProcess P hP).map (ContinuousPath.rescale (Homeomorph.refl alpha) c) := by
  have hid : (⇑(Homeomorph.refl alpha) : alpha → alpha) = id := rfl
  have h : IsRescaledConjugate P P' (Homeomorph.refl alpha) c := by
    intro t x
    rw [htime t, hid, Measure.map_id]
    rfl
  have hcomap : Kernel.comap (continuousProcess P hP)
      (⇑(Homeomorph.refl alpha).symm) (Homeomorph.refl alpha).symm.measurable =
        continuousProcess P hP := Kernel.comap_id' _
  rw [IsConservative.continuousProcess_eq_map_rescale P hP P' hP' hFeller hK hK' hc h, hcomap]

/-- **Pure conjugation.**  If the transition kernels of `P'` are those of `P` conjugated by a
homeomorphism `e` of the state space, then the continuous-path process of `P'` is the process of
`P` started at `e.symm x` and read through `e` at every time. -/
theorem IsConservative.continuousProcess_eq_map_conjugate
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (hK' : P'.KolmogorovRegular hP') {e : alpha ≃ₜ alpha}
    (hconj : ∀ t x, P' t x = ((P t) (e.symm x)).map e) :
    continuousProcess P' hP' =
      (Kernel.comap (continuousProcess P hP) e.symm e.symm.measurable).map
        (ContinuousPath.rescale e 1) := by
  refine IsConservative.continuousProcess_eq_map_rescale P hP P' hP' hFeller hK hK' one_pos ?_
  intro t x
  rw [hconj t x, one_mul]

end OneSpace

end

end SubMarkovKernelSemigroup

end MarkovProcess
