/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointConservative
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingMeasure
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingRealResolvent
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingTransfer

/-!
# The supremum resolvent as a positive `C₀`-contractive resolvent

The supremum resolvent of a family of local resolvents acts on bounded measurable observables.
Two properties of its action on `C₀` are analytic and are hypotheses here: that the value on an
observable vanishing at infinity is again continuous and vanishing at infinity, supplied as a map
`T` together with the identification `hT` of its values, and that the range of `T` is dense.
Additivity, real homogeneity, the operator bound `1 / lam`, positivity and the resolvent identity
are then proved from the extended-real theory, and assemble the supremum resolvent into a
`PositiveC0ContractiveResolvent` (`minimalC0Resolvent`).

The semigroup which that resolvent generates is represented by a sub-Markov kernel semigroup, and
its kernel resolvent is the supremum resolvent again, on every nonnegative measurable observable
(`kernelResolvent_minimalC0Resolvent`): the two potential measures agree on continuous
observables vanishing at infinity, hence everywhere.

If in addition the shift times the supremum resolvent of the constant observable one is one, the
represented semigroup loses no mass (`isConservative_kernelSemigroup_minimalC0Resolvent`), and
the compactified process started at any point almost surely never reaches the added point
(`ae_exitTime_eq_top_minimalC0Resolvent`).  No kernel into the continuous paths of the state
space is produced from that statement.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

section

namespace MarkovProcess

variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  {X : ℕ → Type*} [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)

omit [LocallyCompactSpace alpha] [SecondCountableTopology alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] in
/-- A continuous observable vanishing at infinity is bounded by its norm. -/
private theorem abs_le_norm_c0 (f : C₀(alpha, ℝ)) (y : alpha) : |f y| ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, ← Real.norm_eq_abs]
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF y

section Operator

variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))

/-- **The `C₀` operator of the supremum resolvent** at a positive shift: the value supplied by
the analytic hypothesis `hT`, packaged as a continuous linear map by additivity, real
homogeneity, and the uniform bound `1 / lam`. -/
def minimalC0Operator (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
      T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
    (nu : Semigroup.PositiveShift) : C₀(alpha, ℝ) →L[ℝ] C₀(alpha, ℝ) :=
  LinearMap.mkContinuous
    { toFun := T nu
      map_add' := fun f g ↦ by
        refine DFunLike.ext _ _ fun x ↦ ?_
        rw [hT nu (f + g) x]
        have hsum : minimalResolventReal R emb (nu : ℝ) (fun y ↦ (f + g) y) x =
            minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x +
              minimalResolventReal R emb (nu : ℝ) (fun y ↦ g y) x :=
          minimalResolventReal_add R emb hemb hmono nu.property f.continuous.measurable
            g.continuous.measurable (abs_le_norm_c0 f) (abs_le_norm_c0 g) x
        rw [hsum, ← hT nu f x, ← hT nu g x]
        rfl
      map_smul' := fun c f ↦ by
        refine DFunLike.ext _ _ fun x ↦ ?_
        rw [hT nu (c • f) x]
        have hsmul : minimalResolventReal R emb (nu : ℝ) (fun y ↦ (c • f) y) x =
            c * minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x :=
          minimalResolventReal_smul R emb hemb (nu : ℝ) c f.continuous.measurable x
        rw [hsmul, ← hT nu f x]
        rfl }
    (nu : ℝ)⁻¹ fun f ↦ by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      refine (BoundedContinuousFunction.norm_le
        (mul_nonneg (inv_nonneg.mpr nu.property.le) (norm_nonneg f))).2 fun x ↦ ?_
      have hbound : |minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x| ≤ ‖f‖ / (nu : ℝ) :=
        abs_minimalResolventReal_le R emb hemb nu.property (abs_le_norm_c0 f) x
      rw [Real.norm_eq_abs]
      calc |(T nu f).toBCF x| = |T nu f x| := rfl
        _ = |minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x| := by rw [hT nu f x]
        _ ≤ ‖f‖ / (nu : ℝ) := hbound
        _ = (nu : ℝ)⁻¹ * ‖f‖ := by rw [div_eq_inv_mul]

omit [LocallyCompactSpace alpha] [SecondCountableTopology alpha] in
/-- The bundled minimal `C₀` operator acts by the given family. -/
@[simp] theorem minimalC0Operator_apply (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
      T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
    (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) :
    minimalC0Operator R emb T hemb hmono hT nu f = T nu f := rfl

/-- **The supremum resolvent as a positive `C₀`-contractive resolvent**, from the analytic
hypotheses that its values on `C₀` are again in `C₀` and have dense range. -/
def minimalC0Resolvent (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
      T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
    (hdense : ∀ nu, DenseRange (T nu)) : PositiveC0ContractiveResolvent alpha where
  toContractiveResolvent :=
    { operator := minimalC0Operator R emb T hemb hmono hT
      resolvent_identity := by
        intro a b
        refine ContinuousLinearMap.ext fun f ↦ ?_
        refine DFunLike.ext _ _ fun x ↦ ?_
        have hcomp : ∀ c d : Semigroup.PositiveShift,
            T c (T d f) x = minimalResolventReal R emb (c : ℝ)
              (fun z ↦ minimalResolventReal R emb (d : ℝ) (fun y ↦ f y) z) x := by
          intro c d
          rw [hT c (T d f) x]
          congr 1
          funext z
          exact hT d f z
        have hgoal : T a f x - T b f x =
            ((b : ℝ) - (a : ℝ)) * T a (T b f) x := by
          rcases lt_trichotomy (a : ℝ) (b : ℝ) with hab | hab | hab
          · have heq := minimalResolventReal_resolventEquation R emb hemb hmono a.property hab
              (f := fun y ↦ f y) f.continuous.measurable (abs_le_norm_c0 f) x
            rw [hcomp a b, hT a f x, hT b f x, heq]
            ring
          · have hab' : a = b := Subtype.ext hab
            rw [hab']
            ring
          · have heq := minimalResolventReal_resolventEquation R emb hemb hmono b.property hab
              (f := fun y ↦ f y) f.continuous.measurable (abs_le_norm_c0 f) x
            have hcommute := minimalResolventReal_comm R emb hemb hmono b.property a.property
              (f := fun y ↦ f y) f.continuous.measurable (abs_le_norm_c0 f) x
            rw [hcomp a b, hT a f x, hT b f x, heq, ← hcommute]
            ring
        simpa using hgoal
      opNorm_le_inv := fun nu ↦
        LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr nu.property.le) _
      denseRange := fun nu ↦ hdense nu }
  isPositive := fun nu f hf x ↦ by
    change 0 ≤ T nu f x
    rw [hT nu f x]
    exact minimalResolventReal_nonneg R emb hemb nu.property hf x

omit [LocallyCompactSpace alpha] [SecondCountableTopology alpha] in
/-- The operator of the minimal `C₀` resolvent is the given family, pointwise. -/
@[simp] theorem minimalC0Resolvent_operator_apply (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
      T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
    (hdense : ∀ nu, DenseRange (T nu)) (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ))
    (x : alpha) :
    (minimalC0Resolvent R emb T hemb hmono hT hdense).toContractiveResolvent.operator nu f x =
      minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x :=
  hT nu f x

end Operator

section Identification

variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))
  (hemb : ∀ m, MeasurableEmbedding (emb m))
  (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
    Monotone fun m ↦ localResolvent R emb m nu h y)
  (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
    T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
  (hdense : ∀ nu, DenseRange (T nu))

omit [MetricSpace alpha] [LocallyCompactSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] in
private theorem extend_id (g : alpha → ℝ≥0∞) :
    Function.extend (id : alpha → alpha) g 0 = g := by
  funext y
  exact Function.Injective.extend_apply Function.injective_id g 0 y

/-- **The kernel resolvent of the generated semigroup is the supremum resolvent**, on every
nonnegative measurable observable.  The two potential measures agree on continuous observables
vanishing at infinity, and finite Borel measures on a locally compact second-countable metric
space are determined by those. -/
theorem kernelResolvent_minimalC0Resolvent {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) (x : alpha) :
    (minimalC0Resolvent R emb T hemb hmono hT hdense).kernelSemigroup.kernelResolvent lam f x =
      minimalResolvent R emb lam f x := by
  have := (minimalC0Resolvent R emb T hemb hmono hT
    hdense).kernelSemigroup.isFiniteMeasure_resolventPotential hlam x
  have := isFiniteMeasure_minimalPotential R emb hemb hmono hlam x
  have hc0 : ∀ g : C₀(alpha, ℝ), (∀ y, 0 ≤ g y) →
      ∫⁻ z, Function.extend (id : alpha → alpha) (fun y ↦ ENNReal.ofReal (g y)) 0 z
          ∂(minimalC0Resolvent R emb T hemb hmono hT hdense).kernelSemigroup.resolventPotential
            lam x =
        ∫⁻ y, ENNReal.ofReal (g y) ∂minimalPotential R emb hemb hmono hlam x := by
    intro g hg0
    have hgmeas : Measurable fun y ↦ ENNReal.ofReal (g y) :=
      ENNReal.measurable_ofReal.comp g.continuous.measurable
    rw [extend_id, (minimalC0Resolvent R emb T hemb hmono hT
        hdense).kernelSemigroup.lintegral_resolventPotential lam hgmeas x,
      lintegral_minimalPotential R emb hemb hmono hlam x hgmeas,
      (minimalC0Resolvent R emb T hemb hmono hT hdense).kernelResolvent_ofReal_eq_operator
        ⟨lam, hlam⟩ g hg0 x,
      minimalC0Resolvent_operator_apply R emb T hemb hmono hT hdense ⟨lam, hlam⟩ g x]
    exact ofReal_minimalResolventReal R emb hemb hlam (abs_le_norm_c0 g) hg0 x
  have hmain := lintegral_extend_eq_of_forall_zeroAtInfty (i := (id : alpha → alpha))
    MeasurableEmbedding.id
    ((minimalC0Resolvent R emb T hemb hmono hT hdense).kernelSemigroup.resolventPotential lam x)
    (minimalPotential R emb hemb hmono hlam x) hc0 hf
  rwa [extend_id, (minimalC0Resolvent R emb T hemb hmono hT
      hdense).kernelSemigroup.lintegral_resolventPotential lam hf x,
    lintegral_minimalPotential R emb hemb hmono hlam x hf] at hmain

end Identification

section Conservativity

variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))
  (hemb : ∀ m, MeasurableEmbedding (emb m))
  (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
    Monotone fun m ↦ localResolvent R emb m nu h y)
  (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
    T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
  (hdense : ∀ nu, DenseRange (T nu))

/-- **Conservativity of the represented semigroup.**  If at one positive shift the shift times
the supremum resolvent of the constant observable one is one, the semigroup represented by the
supremum resolvent loses no mass. -/
theorem isConservative_kernelSemigroup_minimalC0Resolvent {lam : ℝ} (hlam : 0 < lam)
    (hone : ∀ x, ENNReal.ofReal lam * minimalResolvent R emb lam (fun _ ↦ 1) x = 1) :
    (minimalC0Resolvent R emb T hemb hmono hT hdense).kernelSemigroup.IsConservative :=
  SubMarkovKernelSemigroup.isConservative_of_kernelResolvent_one _ hlam fun x ↦ by
    rw [kernelResolvent_minimalC0Resolvent R emb T hemb hmono hT hdense hlam measurable_const x]
    exact hone x

/-- **The process almost surely never reaches the added point.**  Under the same hypothesis, the
compactified process of the supremum resolvent, started at any point, almost surely never leaves
the state space. -/
theorem ae_exitTime_eq_top_minimalC0Resolvent
    (hreg : (minimalC0Resolvent R emb T hemb hmono hT hdense).OnePointRegular) {lam : ℝ}
    (hlam : 0 < lam)
    (hone : ∀ x, ENNReal.ofReal lam * minimalResolvent R emb lam (fun _ ↦ 1) x = 1)
    (x : alpha) :
    letI := hreg.metricSpace
    letI := hreg.completeSpace
    ∀ᵐ omega ∂SubMarkovKernelSemigroup.IsConservative.continuousProcess
        (minimalC0Resolvent R emb T hemb hmono hT hdense).onePointKernelSemigroup
        (minimalC0Resolvent R emb T hemb hmono hT
          hdense).isConservative_onePointKernelSemigroup (x : OnePoint alpha),
      ContinuousPath.exitTime (Set.range ((↑) : alpha → OnePoint alpha)) omega = ⊤ := by
  refine hreg.ae_exitTime_eq_top hlam x ?_
  rw [kernelResolvent_minimalC0Resolvent R emb T hemb hmono hT hdense hlam measurable_const x]
  exact hone x

end Conservativity

end MarkovProcess

end

end PortComputability
