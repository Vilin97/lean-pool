/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedSourceOperators
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderHighParity
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileParity
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedProvider
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderRecursiveAdmissibility
public import LeanPool.NavierStokesAndEuler.Euler.PacketProfileRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketJoinedStepRegularity
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketParity
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderPressureLocality
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedEquation
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedParity

/-!
Actual source profiles for the complete high inverse. The primary datum is a
genuine profile with its path/time witnesses; every later forcing is proved
admissible and every later profile is constructed by the two source inverses.
-/

section

/-! The complete history/forward high inverse preserves the actual recursive symmetries. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField.ProfileParity

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion
  EulerLpCylinderTranslation EulerCylinderFieldReflection

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B)
  (hcorrector : O.curlCorrector = D.curlCorrector P)
  (E : CoefficientEven M.T O) (eM : EulerMeanPacketProvider.EvenData M)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  {p : ℕ} {a : ℕ → Profile}

include hT τ hτ hτT B C hmean hhigh hcorrector E eM hSym hF hDM hBH in
theorem joinedStep (hp : 2 ≤ p)
    (G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (a i))
    (H : ∀ i, i < p → ProfileParity M.T (a i)) :
    ProfileParity M.T (EulerPacketProfileRecursion.step O p a) := by
  let F := ProfileRegularity.prefixFields G
  let W := G (p-1) (by omega)
  have Hpre := prefixOdd H
  let hm : Nonempty (EulerMeanPacketProvider.Forcing M (EulerPacketProfileRecursion.meanForce O p
      a)) :=
    ⟨F.meanForcing M C (by omega) W.correctorDerivative W.corrector_time W.pressure⟩
  let hh : Nonempty (EulerTransversePacketProvider.Forcing P D
      (EulerPacketProfileRecursion.highForce O p a)) :=
    ⟨F.highForcing M D hT C hp W.correctorDerivative W.corrector_time W.pressure hmean
      (ProfileRegularity.prefixLocality G) W.pressure_zero⟩
  let GH := Classical.choice hh
  have hmOdd := F.meanForce_odd Hpre C E (by omega) M.T_pos W.correctorDerivative
    W.corrector_time W.pressure (H (p-1) (by omega)).pressure
  have hm0 (t : Icc (0 : ℝ) M.T) (x : Space) :
      EulerPacketProfileRecursion.meanForce O p a (t,(-x,0)) =
        -EulerPacketProfileRecursion.meanForce O p a (t,(x,0)) := by
    simpa only [neg_zero] using hmOdd t x 0
  have hhOdd : JointOdd D.T (EulerPacketProfileRecursion.highForce O p a) :=
    (F.actualHighForce_odd M Hpre C E eM hp W.correctorDerivative W.corrector_time
      W.pressure (H (p-1) (by omega)).pressure hmean).changeTime hT
  refine {
    high := ?_
    mean := ?_
    corrector := ?_
    pressure := ?_
    highPressure := ?_
    meanPressure := ?_ }
  · intro t x θ
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    change (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(-x,-θ)) =
      -(O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(x,θ))
    rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    exact EulerTransversePacketJoin.vector_odd τ hτ hτT B GH hSym hF hDM hBH hhOdd td x θ
  · intro t x θ
    change (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 (t,(-x,-θ)) =
      -(O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).1 (t,(x,θ))
    rw [hmean]
    exact EulerMeanPacketProvider.meanSolve_odd M eM _ hm hm0 t x θ
  · intro t x θ
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    change O.curlCorrector (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1
        (t,(-x,-θ)) =
      -O.curlCorrector (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).1 (t,(x,θ))
    rw [hcorrector,hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    exact EulerTransversePacketJoin.curlCorrector_odd τ hτ hτT B GH hSym hF hDM hBH hhOdd td x θ
  · intro t x θ
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    change pressureGradient (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2
        (t,(-x,-θ)) =
      -pressureGradient (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 (t,(x,θ))
    rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    exact pressureGradient_odd (EulerTransversePacketJoin.scalar τ hτ hτT B GH) t
      (EulerTransversePacketJoin.scalar_smooth τ hτ hτT B GH t)
      (EulerTransversePacketJoin.scalar_even τ hτ hτT B GH hSym hF hDM hBH hhOdd td) x θ
  · intro t x θ
    let td : Icc (0 : ℝ) D.T := ⟨t,by rw [← hT]; exact t.property⟩
    change (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 (t,(-x,-θ)) =
      (O.highSolve (EulerPacketProfileRecursion.highForce O p a)).2 (t,(x,θ))
    rw [hhigh,EulerTransversePacketJoin.highSolve_of_admissible τ hτ hτT B hh]
    exact EulerTransversePacketJoin.scalar_even τ hτ hτT B GH hSym hF hDM hBH hhOdd td x θ
  · intro t x θ
    change (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).2 (t,(-x,-θ)) =
      (O.meanSolve (EulerPacketProfileRecursion.meanForce O p a)).2 (t,(x,θ))
    rw [hmean]
    exact EulerMeanPacketProvider.meanSolve_even M eM _ hm hm0 t x θ

end EulerPacketCylinderField.ProfileParity

end
end

end

section

/-! All-grade admissibility for the actual history/forward packet recursion. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B)
  (hcorrector : O.curlCorrector = D.curlCorrector P)
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

include hT τ hτ hτT B C hmean hhigh hcorrector hprimary in
theorem joined_profiles_regular (p : ℕ) :
    Nonempty (ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary p)) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp0 : p = 0
    · subst p
      rw [profiles_zero]
      exact ⟨ProfileRegularity.zero P M.T M.T_pos.le D.support⟩
    by_cases hp1 : p = 1
    · subst p
      rw [profiles_one]
      exact ⟨hprimary⟩
    have hp : 2 ≤ p := by omega
    let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
      fun i hi => Classical.choice (ih i hi)
    rw [profiles_step O primary p hp]
    exact ⟨ProfileRegularity.joinedStep M D hT τ hτ hτT B C hmean hhigh hcorrector hp G⟩

/-- Joined profile witness, given by `Classical.choice (joined_profiles_regular M D hT τ hτ hτT
B C hmean hhigh hcorrector primary hprimary p)`. -/
def joinedProfileWitness (p : ℕ) :
    ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary p) :=
  Classical.choice (joined_profiles_regular M D hT τ hτ hτT B C hmean hhigh hcorrector primary
      hprimary p)

/-- Joined profiles mean forcing as an element of `EulerMeanPacketProvider.Forcing M (meanForce
O p (profiles O primary))`. -/
def joinedProfilesMeanForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerMeanPacketProvider.Forcing M (meanForce O p (profiles O primary)) := by
  let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
    fun i _ => joinedProfileWitness M D hT τ hτ hτT B C hmean hhigh hcorrector primary hprimary i
  let F := ProfileRegularity.prefixFields G
  let W := G (p-1) (by omega)
  exact F.meanForcing M C (by omega) W.correctorDerivative W.corrector_time W.pressure

/-- Joined profiles high forcing as an element of `EulerTransversePacketProvider.Forcing P D
(highForce O p (profiles O primary))`. -/
def joinedProfilesHighForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerTransversePacketProvider.Forcing P D (highForce O p (profiles O primary)) := by
  let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
    fun i _ => joinedProfileWitness M D hT τ hτ hτT B C hmean hhigh hcorrector primary hprimary i
  let F := ProfileRegularity.prefixFields G
  let W := G (p-1) (by omega)
  exact F.highForcing M D hT C hp W.correctorDerivative W.corrector_time W.pressure hmean
    (ProfileRegularity.prefixLocality G) W.pressure_zero

end EulerPacketCylinderField

end
end

end

section

/-! Every grade constructed with the joined inverse has the prescribed joint parity. -/

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  {O : Operators} (C : CoefficientData P M.T O)
  (hmean : O.meanSolve = EulerMeanPacketProvider.meanSolve M)
  (hhigh : O.highSolve = EulerTransversePacketJoin.highSolve (P := P) τ hτ hτT B)
  (hcorrector : O.curlCorrector = D.curlCorrector P)
  (E : CoefficientEven M.T O) (eM : EulerMeanPacketProvider.EvenData M)
  (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
  (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
  (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
  (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x)
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)
  (hprimaryParity : ProfileParity M.T primary)

include hT τ hτ hτT B C hmean hhigh hcorrector E eM hSym hF hDM hBH hprimary hprimaryParity in
theorem joined_profiles_parity (p : ℕ) : ProfileParity M.T (profiles O primary p) := by
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp0 : p = 0
    · subst p
      rw [profiles_zero]
      exact ProfileParity.zero M.T
    by_cases hp1 : p = 1
    · subst p
      rw [profiles_one]
      exact hprimaryParity
    have hp : 2 ≤ p := by omega
    let G : ∀ i, i < p → ProfileRegularity P M.T M.T_pos.le D.support (profiles O primary i) :=
      fun i _ => joinedProfileWitness M D hT τ hτ hτT B C hmean hhigh hcorrector primary hprimary i
    rw [profiles_step O primary p hp]
    exact ProfileParity.joinedStep M D hT τ hτ hτT B C hmean hhigh hcorrector E eM
      hSym hF hDM hBH hp G ih

end EulerPacketCylinderField

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable (P : ℝ) [Fact (0 < P)] (M : EulerMeanPacketProvider.Data)
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : EulerTransversePacketProvider.Data U) (hT : M.T = D.T)
  (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : EulerTransversePacketProvider.HistoryData (D.initial τ hτ hτT.le))
  (primary : Profile) (hprimary : ProfileRegularity P M.T M.T_pos.le D.support primary)

/-- Joined source profiles, given by `profiles (joinedSourceOperators P M D τ hτ hτT B)
primary`. -/
def joinedSourceProfiles : ℕ → Profile :=
  profiles (joinedSourceOperators P M D τ hτ hτT B) primary

/-- Joined source profile witness, given by `joinedProfileWitness M D hT τ hτ hτT B
(joinedSourceCoefficientData P M D τ hτ hτT B hT) rfl rfl rfl primary hprimary p`. -/
def joinedSourceProfileWitness (p : ℕ) :
    ProfileRegularity P M.T M.T_pos.le D.support (joinedSourceProfiles P M D τ hτ hτT B primary p)
        :=
  joinedProfileWitness M D hT τ hτ hτT B (joinedSourceCoefficientData P M D τ hτ hτT B hT)
    rfl rfl rfl primary hprimary p

/-- Joined source mean forcing, given by `joinedProfilesMeanForcing M D hT τ hτ hτT B
(joinedSourceCoefficientData P M D τ hτ hτT B hT) rfl rfl rfl primary hprimary p hp`. -/
def joinedSourceMeanForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerMeanPacketProvider.Forcing M
      (meanForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary)) :=
  joinedProfilesMeanForcing M D hT τ hτ hτT B (joinedSourceCoefficientData P M D τ hτ hτT B hT)
    rfl rfl rfl primary hprimary p hp

/-- Joined source high forcing, given by `joinedProfilesHighForcing M D hT τ hτ hτT B
(joinedSourceCoefficientData P M D τ hτ hτT B hT) rfl rfl rfl primary hprimary p hp`. -/
def joinedSourceHighForcing (p : ℕ) (hp : 2 ≤ p) :
    EulerTransversePacketProvider.Forcing P D
      (highForce (joinedSourceOperators P M D τ hτ hτT B) p
        (joinedSourceProfiles P M D τ hτ hτT B primary)) :=
  joinedProfilesHighForcing M D hT τ hτ hτT B (joinedSourceCoefficientData P M D τ hτ hτT B hT)
    rfl rfl rfl primary hprimary p hp

theorem joinedSourceCoefficientEven
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x) :
    CoefficientEven M.T (joinedSourceOperators P M D τ hτ hτT B) where
  inverse t x _ := D.inverse_even hF (D.clamp t) x
  strain t x _ := hM (D.clamp t) x
  normal t x _ := D.normal_even hF (D.clamp t) x

include hT hprimary in
theorem joinedSourceProfiles_parity
    (eM : EulerMeanPacketProvider.EvenData M)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hDM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hBH : ∀ t x, B.H.field t (-x) = B.H.field t x)
    (hprimaryParity : ProfileParity M.T primary) (p : ℕ) :
    ProfileParity M.T (joinedSourceProfiles P M D τ hτ hτT B primary p) :=
  joined_profiles_parity M D hT τ hτ hτT B (joinedSourceCoefficientData P M D τ hτ hτT B hT)
    rfl rfl rfl (joinedSourceCoefficientEven P M D τ hτ hτT B hF hDM) eM
    hSym hF hDM hBH primary hprimary hprimaryParity p

end EulerPacketCylinderField
