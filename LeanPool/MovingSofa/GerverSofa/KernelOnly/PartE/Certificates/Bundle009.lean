/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch010`.
* `GerverSofa.KernelOnly.PartE.Certificates.Batch029`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCellse8870ef6ec

/-- Subcell `0111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0112 : AngleCell :=
  childHL (childLH (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0113 : AngleCell :=
  childHH (childLH (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0120 : AngleCell :=
  childLL (childHL (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0121 : AngleCell :=
  childLH (childHL (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0122 : AngleCell :=
  childHL (childHL (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0123 : AngleCell :=
  childHH (childHL (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0130 : AngleCell :=
  childLL (childHH (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0131 : AngleCell :=
  childLH (childHH (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0132 : AngleCell :=
  childHL (childHH (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `0133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0133 : AngleCell :=
  childHH (childHH (childLH (childLL e24ThetaAboveRoot)))

/-- Subcell `1000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24ThetaAboveRoot)))

/-- Subcell `01113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell0111)))

/-- Subcell `01113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell0111)))

/-- Subcell `01113333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell01113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell0111)))

/-- Subcell `10002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell1000)))

/-- Subcell `10002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell1000)))

/-- Subcell `10002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell1000)))

/-- Subcell `10002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell1000)))

/-- Subcell `10002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell1000)))

/-- Subcell `10002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell1000)))

/-- Subcell `10002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell1000)))

/-- Subcell `10002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell1000)))

/-- Subcell `10002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell1000)))

/-- Subcell `10002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell1000)))

/-- Subcell `10002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell1000)))

/-- Subcell `10002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell1000)))

/-- Subcell `10002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell1000)))

/-- Subcell `10002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell1000)))

/-- Subcell `10002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell1000)))

/-- Subcell `10002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell1000)))

/-- Subcell `10002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002220 : AngleCell :=
  childLL (childHL (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002221 : AngleCell :=
  childLH (childHL (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002222 : AngleCell :=
  childHL (childHL (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002223 : AngleCell :=
  childHH (childHL (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002230 : AngleCell :=
  childLL (childHH (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002231 : AngleCell :=
  childLH (childHH (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002232 : AngleCell :=
  childHL (childHH (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002233 : AngleCell :=
  childHH (childHH (childHL (childHL thetaAboveCell1000)))

/-- Subcell `10002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002320 : AngleCell :=
  childLL (childHL (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002321 : AngleCell :=
  childLH (childHL (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002322 : AngleCell :=
  childHL (childHL (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002323 : AngleCell :=
  childHH (childHL (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002330 : AngleCell :=
  childLL (childHH (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10002333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10002333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1000)))

/-- Subcell `10003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell1000)))

/-- Subcell `10003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell1000)))

/-- Subcell `10003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell1000)))

/-- Subcell `10003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell1000)))

/-- Subcell `10003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell1000)))

/-- Subcell `10003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell1000)))

/-- Subcell `10003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell1000)))

/-- Subcell `10003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell1000)))

/-- Subcell `10003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell1000)))

/-- Subcell `10003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell1000)))

/-- Subcell `10003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell1000)))

/-- Subcell `10003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell1000)))

/-- Subcell `10003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell1000)))

/-- Subcell `10003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell1000)))

/-- Subcell `10003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell1000)))

/-- Subcell `10003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell1000)))

/-- Subcell `10003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1000)))

/-- Subcell `10003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell10003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1000)))

end GerverSofa.PartE.CertificateCellse8870ef6ec

namespace GerverSofa.PartE.CertificateCells7b7ba6d809

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell0000)))

/-- Subcell `00003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `000032012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003201)))

/-- Subcell `000032012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003201)))

/-- Subcell `000032013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003201)))

/-- Subcell `000032013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003201)))

/-- Subcell `000032102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003210)))

/-- Subcell `000032102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003210)))

/-- Subcell `000032103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003210)))

/-- Subcell `000032103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003210)))

/-- Subcell `000032112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003211)))

/-- Subcell `000032112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003211)))

/-- Subcell `000032113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003211)))

/-- Subcell `000032113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000032113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000032113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003211)))

/-- Subcell `000033002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003300)))

/-- Subcell `000033002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003300)))

/-- Subcell `000033003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003300)))

/-- Subcell `000033003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003300)))

/-- Subcell `000033012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00003301)))

/-- Subcell `000033012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00003301)))

/-- Subcell `000033012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00003301)))

/-- Subcell `000033013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00003301)))

/-- Subcell `000033013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00003301)))

/-- Subcell `000033013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00003301)))

/-- Subcell `000033102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003310)))

end GerverSofa.PartE.CertificateCells7b7ba6d809

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT358400010`.
-/

public section

noncomputable section

section

/-! E24KC5 checkpoint-aware kernel batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse8870ef6ec

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellse8870ef6ec

open CertificateCellse8870ef6ec
theorem e24KC2ThetaAboveLeaf0111320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113202)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113202)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113202)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113202)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113202)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113202)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113202)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113202)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113202)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113202)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113202)) h
theorem e24KC2ThetaAboveLeaf0111320300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113203)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113203)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113203)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113203)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113203)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113203)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113203)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113203)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113203)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113203)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113203)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113203)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113203)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113203)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113203)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf0111320333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113203)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113203)) h
theorem e24KC2ThetaAboveLeaf011132100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113210) = true := by
  have h : ((childLL thetaAboveCell01113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113210) h
theorem e24KC2ThetaAboveLeaf011132101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113210) = true := by
  have h : ((childLH thetaAboveCell01113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113210) h
theorem e24KC2ThetaAboveLeaf011132102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113210) = true := by
  have h : ((childHL thetaAboveCell01113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113210) h
theorem e24KC2ThetaAboveLeaf011132103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113210) = true := by
  have h : ((childHH thetaAboveCell01113210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113210) h
theorem e24KC2ThetaAboveLeaf011132110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113211) = true := by
  have h : ((childLL thetaAboveCell01113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113211) h
theorem e24KC2ThetaAboveLeaf011132111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113211) = true := by
  have h : ((childLH thetaAboveCell01113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113211) h
theorem e24KC2ThetaAboveLeaf011132112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113211) = true := by
  have h : ((childHL thetaAboveCell01113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113211) h
theorem e24KC2ThetaAboveLeaf011132113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113211) = true := by
  have h : ((childHH thetaAboveCell01113211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113211) h
theorem e24KC2ThetaAboveLeaf0111321200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113212)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113212)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113212)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113212)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113212)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113212)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113212)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113212)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113212)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113212)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113212)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113212)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113212)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113212)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113212)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113212)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113212)) h
theorem e24KC2ThetaAboveLeaf0111321300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113213)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113213)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113213)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113213)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113213)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113213)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113213)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113213)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113213)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113213)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113213)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113213)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113213)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113213)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113213)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf0111321333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113213)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113213)) h
theorem e24KC2ThetaAboveLeaf011132200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113220) = true := by
  have h : ((childLL thetaAboveCell01113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113220) h
theorem e24KC2ThetaAboveLeaf011132201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113220) = true := by
  have h : ((childLH thetaAboveCell01113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113220) h
theorem e24KC2ThetaAboveLeaf011132202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113220) = true := by
  have h : ((childHL thetaAboveCell01113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113220) h
theorem e24KC2ThetaAboveLeaf011132203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113220) = true := by
  have h : ((childHH thetaAboveCell01113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113220) h
theorem e24KC2ThetaAboveLeaf011132210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113221) = true := by
  have h : ((childLL thetaAboveCell01113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113221) h
theorem e24KC2ThetaAboveLeaf011132211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113221) = true := by
  have h : ((childLH thetaAboveCell01113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113221) h
theorem e24KC2ThetaAboveLeaf011132212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113221) = true := by
  have h : ((childHL thetaAboveCell01113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113221) h
theorem e24KC2ThetaAboveLeaf011132213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113221) = true := by
  have h : ((childHH thetaAboveCell01113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113221) h
theorem e24KC2ThetaAboveLeaf01113222 :
    adaptiveCoverCheck 11 thetaAboveCell01113222 = true := by
  have h : (thetaAboveCell01113222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113222 h
theorem e24KC2ThetaAboveLeaf01113223 :
    adaptiveCoverCheck 11 thetaAboveCell01113223 = true := by
  have h : (thetaAboveCell01113223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113223 h
theorem e24KC2ThetaAboveLeaf011132300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113230) = true := by
  have h : ((childLL thetaAboveCell01113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113230) h
theorem e24KC2ThetaAboveLeaf011132301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113230) = true := by
  have h : ((childLH thetaAboveCell01113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113230) h
theorem e24KC2ThetaAboveLeaf011132302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113230) = true := by
  have h : ((childHL thetaAboveCell01113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113230) h
theorem e24KC2ThetaAboveLeaf011132303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113230) = true := by
  have h : ((childHH thetaAboveCell01113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113230) h
theorem e24KC2ThetaAboveLeaf011132310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113231) = true := by
  have h : ((childLL thetaAboveCell01113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113231) h
theorem e24KC2ThetaAboveLeaf011132311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113231) = true := by
  have h : ((childLH thetaAboveCell01113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113231) h
theorem e24KC2ThetaAboveLeaf011132312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113231) = true := by
  have h : ((childHL thetaAboveCell01113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113231) h
theorem e24KC2ThetaAboveLeaf011132313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113231) = true := by
  have h : ((childHH thetaAboveCell01113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113231) h
theorem e24KC2ThetaAboveLeaf01113232 :
    adaptiveCoverCheck 11 thetaAboveCell01113232 = true := by
  have h : (thetaAboveCell01113232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113232 h
theorem e24KC2ThetaAboveLeaf01113233 :
    adaptiveCoverCheck 11 thetaAboveCell01113233 = true := by
  have h : (thetaAboveCell01113233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113233 h
theorem e24KC2ThetaAboveLeaf011133000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113300) = true := by
  have h : ((childLL thetaAboveCell01113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113300) h
theorem e24KC2ThetaAboveLeaf011133001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113300) = true := by
  have h : ((childLH thetaAboveCell01113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113300) h
theorem e24KC2ThetaAboveLeaf011133002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113300) = true := by
  have h : ((childHL thetaAboveCell01113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113300) h
theorem e24KC2ThetaAboveLeaf011133003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113300) = true := by
  have h : ((childHH thetaAboveCell01113300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113300) h
theorem e24KC2ThetaAboveLeaf011133010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113301) = true := by
  have h : ((childLL thetaAboveCell01113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113301) h
theorem e24KC2ThetaAboveLeaf011133011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113301) = true := by
  have h : ((childLH thetaAboveCell01113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113301) h
theorem e24KC2ThetaAboveLeaf011133012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113301) = true := by
  have h : ((childHL thetaAboveCell01113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113301) h
theorem e24KC2ThetaAboveLeaf011133013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113301) = true := by
  have h : ((childHH thetaAboveCell01113301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113301) h
theorem e24KC2ThetaAboveLeaf0111330200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113302)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113302)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113302)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113302)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113302)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113302)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113302)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113302)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113302)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113302)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113302)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113302)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113302)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113302)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113302)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113302)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113302)) h
theorem e24KC2ThetaAboveLeaf0111330300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113303)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113303)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113303)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113303)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113303)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113303)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113303)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113303)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113303)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113303)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113303)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113303)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113303)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113303)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113303)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf0111330333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113303)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113303)) h
theorem e24KC2ThetaAboveLeaf011133100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113310) = true := by
  have h : ((childLL thetaAboveCell01113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113310) h
theorem e24KC2ThetaAboveLeaf011133101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113310) = true := by
  have h : ((childLH thetaAboveCell01113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113310) h
theorem e24KC2ThetaAboveLeaf011133102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113310) = true := by
  have h : ((childHL thetaAboveCell01113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113310) h
theorem e24KC2ThetaAboveLeaf011133103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113310) = true := by
  have h : ((childHH thetaAboveCell01113310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113310) h
theorem e24KC2ThetaAboveLeaf011133110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113311) = true := by
  have h : ((childLL thetaAboveCell01113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113311) h
theorem e24KC2ThetaAboveLeaf011133111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113311) = true := by
  have h : ((childLH thetaAboveCell01113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113311) h
theorem e24KC2ThetaAboveLeaf011133112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113311) = true := by
  have h : ((childHL thetaAboveCell01113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113311) h
theorem e24KC2ThetaAboveLeaf011133113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113311) = true := by
  have h : ((childHH thetaAboveCell01113311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113311) h
theorem e24KC2ThetaAboveLeaf0111331200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113312)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113312)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113312)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113312)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113312)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113312)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113312)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113312)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113312)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113312)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113312)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113312)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113312)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113312)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113312)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113312)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113312)) h
theorem e24KC2ThetaAboveLeaf0111331300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell01113313)) = true := by
  have h : ((childLL (childLL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell01113313)) = true := by
  have h : ((childLH (childLL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell01113313)) = true := by
  have h : ((childHL (childLL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell01113313)) = true := by
  have h : ((childHH (childLL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell01113313)) = true := by
  have h : ((childLL (childLH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell01113313)) = true := by
  have h : ((childLH (childLH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell01113313)) = true := by
  have h : ((childHL (childLH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell01113313)) = true := by
  have h : ((childHH (childLH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell01113313)) = true := by
  have h : ((childLL (childHL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell01113313)) = true := by
  have h : ((childLH (childHL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell01113313)) = true := by
  have h : ((childHL (childHL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell01113313)) = true := by
  have h : ((childHH (childHL thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell01113313)) = true := by
  have h : ((childLL (childHH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell01113313)) = true := by
  have h : ((childLH (childHH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell01113313)) = true := by
  have h : ((childHL (childHH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf0111331333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell01113313)) = true := by
  have h : ((childHH (childHH thetaAboveCell01113313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell01113313)) h
theorem e24KC2ThetaAboveLeaf011133200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113320) = true := by
  have h : ((childLL thetaAboveCell01113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113320) h
theorem e24KC2ThetaAboveLeaf011133201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113320) = true := by
  have h : ((childLH thetaAboveCell01113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113320) h
theorem e24KC2ThetaAboveLeaf011133202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113320) = true := by
  have h : ((childHL thetaAboveCell01113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113320) h
theorem e24KC2ThetaAboveLeaf011133203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113320) = true := by
  have h : ((childHH thetaAboveCell01113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113320) h
theorem e24KC2ThetaAboveLeaf011133210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113321) = true := by
  have h : ((childLL thetaAboveCell01113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113321) h
theorem e24KC2ThetaAboveLeaf011133211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113321) = true := by
  have h : ((childLH thetaAboveCell01113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113321) h
theorem e24KC2ThetaAboveLeaf011133212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113321) = true := by
  have h : ((childHL thetaAboveCell01113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113321) h
theorem e24KC2ThetaAboveLeaf011133213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113321) = true := by
  have h : ((childHH thetaAboveCell01113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113321) h
theorem e24KC2ThetaAboveLeaf01113322 :
    adaptiveCoverCheck 11 thetaAboveCell01113322 = true := by
  have h : (thetaAboveCell01113322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113322 h
theorem e24KC2ThetaAboveLeaf01113323 :
    adaptiveCoverCheck 11 thetaAboveCell01113323 = true := by
  have h : (thetaAboveCell01113323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113323 h
theorem e24KC2ThetaAboveLeaf011133300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113330) = true := by
  have h : ((childLL thetaAboveCell01113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113330) h
theorem e24KC2ThetaAboveLeaf011133301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113330) = true := by
  have h : ((childLH thetaAboveCell01113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113330) h
theorem e24KC2ThetaAboveLeaf011133302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113330) = true := by
  have h : ((childHL thetaAboveCell01113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113330) h
theorem e24KC2ThetaAboveLeaf011133303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113330) = true := by
  have h : ((childHH thetaAboveCell01113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113330) h
theorem e24KC2ThetaAboveLeaf011133310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell01113331) = true := by
  have h : ((childLL thetaAboveCell01113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell01113331) h
theorem e24KC2ThetaAboveLeaf011133311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell01113331) = true := by
  have h : ((childLH thetaAboveCell01113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell01113331) h
theorem e24KC2ThetaAboveLeaf011133312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell01113331) = true := by
  have h : ((childHL thetaAboveCell01113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell01113331) h
theorem e24KC2ThetaAboveLeaf011133313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell01113331) = true := by
  have h : ((childHH thetaAboveCell01113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell01113331) h
theorem e24KC2ThetaAboveLeaf01113332 :
    adaptiveCoverCheck 11 thetaAboveCell01113332 = true := by
  have h : (thetaAboveCell01113332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113332 h
theorem e24KC2ThetaAboveLeaf01113333 :
    adaptiveCoverCheck 11 thetaAboveCell01113333 = true := by
  have h : (thetaAboveCell01113333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell01113333 h
theorem e24KC2ThetaAboveLeaf0112000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0112))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0112))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0112))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0112))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0112))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0112))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0112))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0112))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf011202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0112)) = true := by
  have h : ((childHL (childLL thetaAboveCell0112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0112)) h
theorem e24KC2ThetaAboveLeaf011203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0112)) = true := by
  have h : ((childHH (childLL thetaAboveCell0112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0112)) h
theorem e24KC2ThetaAboveLeaf0112100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0112))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0112))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0112))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0112))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0112))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0112))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0112))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf0112113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0112))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0112))) h
theorem e24KC2ThetaAboveLeaf011212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0112)) = true := by
  have h : ((childHL (childLH thetaAboveCell0112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0112)) h
theorem e24KC2ThetaAboveLeaf011213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0112)) = true := by
  have h : ((childHH (childLH thetaAboveCell0112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0112)) h
theorem e24KC2ThetaAboveLeaf01122 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0112) = true := by
  have h : ((childHL thetaAboveCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0112) h
theorem e24KC2ThetaAboveLeaf01123 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0112) = true := by
  have h : ((childHH thetaAboveCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0112) h
theorem e24KC2ThetaAboveLeaf0113000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell0113))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell0113))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell0113))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell0113))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell0113))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell0113))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell0113))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell0113))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf011302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell0113)) = true := by
  have h : ((childHL (childLL thetaAboveCell0113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell0113)) h
theorem e24KC2ThetaAboveLeaf011303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell0113)) = true := by
  have h : ((childHH (childLL thetaAboveCell0113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell0113)) h
theorem e24KC2ThetaAboveLeaf0113100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell0113))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell0113))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell0113))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell0113))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell0113))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell0113))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell0113))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf0113113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell0113))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell0113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell0113))) h
theorem e24KC2ThetaAboveLeaf011312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell0113)) = true := by
  have h : ((childHL (childLH thetaAboveCell0113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell0113)) h
theorem e24KC2ThetaAboveLeaf011313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell0113)) = true := by
  have h : ((childHH (childLH thetaAboveCell0113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell0113)) h
theorem e24KC2ThetaAboveLeaf01132 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell0113) = true := by
  have h : ((childHL thetaAboveCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell0113) h
theorem e24KC2ThetaAboveLeaf01133 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell0113) = true := by
  have h : ((childHH thetaAboveCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell0113) h
theorem e24KC2ThetaAboveLeaf0120 :
    adaptiveCoverCheck 15 thetaAboveCell0120 = true := by
  have h : (thetaAboveCell0120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0120 h
theorem e24KC2ThetaAboveLeaf0121 :
    adaptiveCoverCheck 15 thetaAboveCell0121 = true := by
  have h : (thetaAboveCell0121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0121 h
theorem e24KC2ThetaAboveLeaf0122 :
    adaptiveCoverCheck 15 thetaAboveCell0122 = true := by
  have h : (thetaAboveCell0122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0122 h
theorem e24KC2ThetaAboveLeaf0123 :
    adaptiveCoverCheck 15 thetaAboveCell0123 = true := by
  have h : (thetaAboveCell0123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0123 h
theorem e24KC2ThetaAboveLeaf0130 :
    adaptiveCoverCheck 15 thetaAboveCell0130 = true := by
  have h : (thetaAboveCell0130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0130 h
theorem e24KC2ThetaAboveLeaf0131 :
    adaptiveCoverCheck 15 thetaAboveCell0131 = true := by
  have h : (thetaAboveCell0131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0131 h
theorem e24KC2ThetaAboveLeaf0132 :
    adaptiveCoverCheck 15 thetaAboveCell0132 = true := by
  have h : (thetaAboveCell0132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0132 h
theorem e24KC2ThetaAboveLeaf0133 :
    adaptiveCoverCheck 15 thetaAboveCell0133 = true := by
  have h : (thetaAboveCell0133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell0133 h
theorem e24KC2ThetaAboveLeaf020 :
    adaptiveCoverCheck 16 (childLL (childHL (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf021 :
    adaptiveCoverCheck 16 (childLH (childHL (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf022 :
    adaptiveCoverCheck 16 (childHL (childHL (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHL (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHL (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf023 :
    adaptiveCoverCheck 16 (childHH (childHL (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf030 :
    adaptiveCoverCheck 16 (childLL (childHH (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf031 :
    adaptiveCoverCheck 16 (childLH (childHH (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf032 :
    adaptiveCoverCheck 16 (childHL (childHH (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf033 :
    adaptiveCoverCheck 16 (childHH (childHH (childLL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childLL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childLL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf100000 :
    adaptiveCoverCheck 13 (childLL (childLL thetaAboveCell1000)) = true := by
  have h : ((childLL (childLL thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLL thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100001 :
    adaptiveCoverCheck 13 (childLH (childLL thetaAboveCell1000)) = true := by
  have h : ((childLH (childLL thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLL thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100002 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1000)) = true := by
  have h : ((childHL (childLL thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100003 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1000)) = true := by
  have h : ((childHH (childLL thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100010 :
    adaptiveCoverCheck 13 (childLL (childLH thetaAboveCell1000)) = true := by
  have h : ((childLL (childLH thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL (childLH thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100011 :
    adaptiveCoverCheck 13 (childLH (childLH thetaAboveCell1000)) = true := by
  have h : ((childLH (childLH thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH (childLH thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100012 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1000)) = true := by
  have h : ((childHL (childLH thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf100013 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1000)) = true := by
  have h : ((childHH (childLH thetaAboveCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1000)) h
theorem e24KC2ThetaAboveLeaf1000200 :
    adaptiveCoverCheck 12 (childLL (childLL (childHL thetaAboveCell1000))) = true := by
  have h : ((childLL (childLL (childHL thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHL thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf1000201 :
    adaptiveCoverCheck 12 (childLH (childLL (childHL thetaAboveCell1000))) = true := by
  have h : ((childLH (childLL (childHL thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHL thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf10002020 :
    adaptiveCoverCheck 11 thetaAboveCell10002020 = true := by
  have h : (thetaAboveCell10002020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002020 h
theorem e24KC2ThetaAboveLeaf10002021 :
    adaptiveCoverCheck 11 thetaAboveCell10002021 = true := by
  have h : (thetaAboveCell10002021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002021 h
theorem e24KC2ThetaAboveLeaf10002022 :
    adaptiveCoverCheck 11 thetaAboveCell10002022 = true := by
  have h : (thetaAboveCell10002022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002022 h
theorem e24KC2ThetaAboveLeaf10002023 :
    adaptiveCoverCheck 11 thetaAboveCell10002023 = true := by
  have h : (thetaAboveCell10002023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002023 h
theorem e24KC2ThetaAboveLeaf10002030 :
    adaptiveCoverCheck 11 thetaAboveCell10002030 = true := by
  have h : (thetaAboveCell10002030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002030 h
theorem e24KC2ThetaAboveLeaf10002031 :
    adaptiveCoverCheck 11 thetaAboveCell10002031 = true := by
  have h : (thetaAboveCell10002031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002031 h
theorem e24KC2ThetaAboveLeaf10002032 :
    adaptiveCoverCheck 11 thetaAboveCell10002032 = true := by
  have h : (thetaAboveCell10002032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002032 h
theorem e24KC2ThetaAboveLeaf10002033 :
    adaptiveCoverCheck 11 thetaAboveCell10002033 = true := by
  have h : (thetaAboveCell10002033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002033 h
theorem e24KC2ThetaAboveLeaf1000210 :
    adaptiveCoverCheck 12 (childLL (childLH (childHL thetaAboveCell1000))) = true := by
  have h : ((childLL (childLH (childHL thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHL thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf1000211 :
    adaptiveCoverCheck 12 (childLH (childLH (childHL thetaAboveCell1000))) = true := by
  have h : ((childLH (childLH (childHL thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHL thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf10002120 :
    adaptiveCoverCheck 11 thetaAboveCell10002120 = true := by
  have h : (thetaAboveCell10002120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002120 h
theorem e24KC2ThetaAboveLeaf10002121 :
    adaptiveCoverCheck 11 thetaAboveCell10002121 = true := by
  have h : (thetaAboveCell10002121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002121 h
theorem e24KC2ThetaAboveLeaf10002122 :
    adaptiveCoverCheck 11 thetaAboveCell10002122 = true := by
  have h : (thetaAboveCell10002122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002122 h
theorem e24KC2ThetaAboveLeaf10002123 :
    adaptiveCoverCheck 11 thetaAboveCell10002123 = true := by
  have h : (thetaAboveCell10002123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002123 h
theorem e24KC2ThetaAboveLeaf10002130 :
    adaptiveCoverCheck 11 thetaAboveCell10002130 = true := by
  have h : (thetaAboveCell10002130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002130 h
theorem e24KC2ThetaAboveLeaf10002131 :
    adaptiveCoverCheck 11 thetaAboveCell10002131 = true := by
  have h : (thetaAboveCell10002131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002131 h
theorem e24KC2ThetaAboveLeaf10002132 :
    adaptiveCoverCheck 11 thetaAboveCell10002132 = true := by
  have h : (thetaAboveCell10002132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002132 h
theorem e24KC2ThetaAboveLeaf10002133 :
    adaptiveCoverCheck 11 thetaAboveCell10002133 = true := by
  have h : (thetaAboveCell10002133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002133 h
theorem e24KC2ThetaAboveLeaf100022000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002200) = true := by
  have h : ((childLL thetaAboveCell10002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002200) h
theorem e24KC2ThetaAboveLeaf100022001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002200) = true := by
  have h : ((childLH thetaAboveCell10002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002200) h
theorem e24KC2ThetaAboveLeaf100022002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002200) = true := by
  have h : ((childHL thetaAboveCell10002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002200) h
theorem e24KC2ThetaAboveLeaf100022003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002200) = true := by
  have h : ((childHH thetaAboveCell10002200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002200) h
theorem e24KC2ThetaAboveLeaf100022010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002201) = true := by
  have h : ((childLL thetaAboveCell10002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002201) h
theorem e24KC2ThetaAboveLeaf100022011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002201) = true := by
  have h : ((childLH thetaAboveCell10002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002201) h
theorem e24KC2ThetaAboveLeaf100022012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002201) = true := by
  have h : ((childHL thetaAboveCell10002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002201) h
theorem e24KC2ThetaAboveLeaf100022013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002201) = true := by
  have h : ((childHH thetaAboveCell10002201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002201) h
theorem e24KC2ThetaAboveLeaf1000220200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002202)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002202)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002202)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002202)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002202)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002202)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002202)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002202)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002202)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002202)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002202)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002202)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002202)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002202)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002202)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002202)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002202)) h
theorem e24KC2ThetaAboveLeaf1000220300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002203)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002203)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002203)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002203)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002203)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002203)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002203)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002203)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002203)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002203)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002203)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002203)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002203)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002203)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002203)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf1000220333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002203)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002203))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002203)) h
theorem e24KC2ThetaAboveLeaf100022100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002210) = true := by
  have h : ((childLL thetaAboveCell10002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002210) h
theorem e24KC2ThetaAboveLeaf100022101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002210) = true := by
  have h : ((childLH thetaAboveCell10002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002210) h
theorem e24KC2ThetaAboveLeaf100022102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002210) = true := by
  have h : ((childHL thetaAboveCell10002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002210) h
theorem e24KC2ThetaAboveLeaf100022103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002210) = true := by
  have h : ((childHH thetaAboveCell10002210)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002210) h
theorem e24KC2ThetaAboveLeaf100022110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002211) = true := by
  have h : ((childLL thetaAboveCell10002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002211) h
theorem e24KC2ThetaAboveLeaf100022111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002211) = true := by
  have h : ((childLH thetaAboveCell10002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002211) h
theorem e24KC2ThetaAboveLeaf100022112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002211) = true := by
  have h : ((childHL thetaAboveCell10002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002211) h
theorem e24KC2ThetaAboveLeaf100022113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002211) = true := by
  have h : ((childHH thetaAboveCell10002211)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002211) h
theorem e24KC2ThetaAboveLeaf1000221200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002212)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002212)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002212)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002212)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002212)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002212)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002212)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002212)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002212)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002212)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002212)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002212)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002212)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002212)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002212)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002212)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002212))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002212)) h
theorem e24KC2ThetaAboveLeaf1000221300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002213)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002213)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002213)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002213)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002213)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002213)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002213)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002213)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002213)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002213)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002213)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002213)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002213)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002213)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002213)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf1000221333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002213)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002213))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002213)) h
theorem e24KC2ThetaAboveLeaf100022200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002220) = true := by
  have h : ((childLL thetaAboveCell10002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002220) h
theorem e24KC2ThetaAboveLeaf100022201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002220) = true := by
  have h : ((childLH thetaAboveCell10002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002220) h
theorem e24KC2ThetaAboveLeaf100022202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002220) = true := by
  have h : ((childHL thetaAboveCell10002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002220) h
theorem e24KC2ThetaAboveLeaf100022203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002220) = true := by
  have h : ((childHH thetaAboveCell10002220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002220) h
theorem e24KC2ThetaAboveLeaf100022210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002221) = true := by
  have h : ((childLL thetaAboveCell10002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002221) h
theorem e24KC2ThetaAboveLeaf100022211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002221) = true := by
  have h : ((childLH thetaAboveCell10002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002221) h
theorem e24KC2ThetaAboveLeaf100022212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002221) = true := by
  have h : ((childHL thetaAboveCell10002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002221) h
theorem e24KC2ThetaAboveLeaf100022213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002221) = true := by
  have h : ((childHH thetaAboveCell10002221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002221) h
theorem e24KC2ThetaAboveLeaf10002222 :
    adaptiveCoverCheck 11 thetaAboveCell10002222 = true := by
  have h : (thetaAboveCell10002222).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002222 h
theorem e24KC2ThetaAboveLeaf10002223 :
    adaptiveCoverCheck 11 thetaAboveCell10002223 = true := by
  have h : (thetaAboveCell10002223).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002223 h
theorem e24KC2ThetaAboveLeaf100022300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002230) = true := by
  have h : ((childLL thetaAboveCell10002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002230) h
theorem e24KC2ThetaAboveLeaf100022301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002230) = true := by
  have h : ((childLH thetaAboveCell10002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002230) h
theorem e24KC2ThetaAboveLeaf100022302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002230) = true := by
  have h : ((childHL thetaAboveCell10002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002230) h
theorem e24KC2ThetaAboveLeaf100022303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002230) = true := by
  have h : ((childHH thetaAboveCell10002230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002230) h
theorem e24KC2ThetaAboveLeaf100022310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002231) = true := by
  have h : ((childLL thetaAboveCell10002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002231) h
theorem e24KC2ThetaAboveLeaf100022311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002231) = true := by
  have h : ((childLH thetaAboveCell10002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002231) h
theorem e24KC2ThetaAboveLeaf100022312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002231) = true := by
  have h : ((childHL thetaAboveCell10002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002231) h
theorem e24KC2ThetaAboveLeaf100022313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002231) = true := by
  have h : ((childHH thetaAboveCell10002231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002231) h
theorem e24KC2ThetaAboveLeaf10002232 :
    adaptiveCoverCheck 11 thetaAboveCell10002232 = true := by
  have h : (thetaAboveCell10002232).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002232 h
theorem e24KC2ThetaAboveLeaf10002233 :
    adaptiveCoverCheck 11 thetaAboveCell10002233 = true := by
  have h : (thetaAboveCell10002233).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002233 h
theorem e24KC2ThetaAboveLeaf100023000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002300) = true := by
  have h : ((childLL thetaAboveCell10002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002300) h
theorem e24KC2ThetaAboveLeaf100023001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002300) = true := by
  have h : ((childLH thetaAboveCell10002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002300) h
theorem e24KC2ThetaAboveLeaf100023002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002300) = true := by
  have h : ((childHL thetaAboveCell10002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002300) h
theorem e24KC2ThetaAboveLeaf100023003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002300) = true := by
  have h : ((childHH thetaAboveCell10002300)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002300) h
theorem e24KC2ThetaAboveLeaf100023010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002301) = true := by
  have h : ((childLL thetaAboveCell10002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002301) h
theorem e24KC2ThetaAboveLeaf100023011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002301) = true := by
  have h : ((childLH thetaAboveCell10002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002301) h
theorem e24KC2ThetaAboveLeaf100023012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002301) = true := by
  have h : ((childHL thetaAboveCell10002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002301) h
theorem e24KC2ThetaAboveLeaf100023013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002301) = true := by
  have h : ((childHH thetaAboveCell10002301)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002301) h
theorem e24KC2ThetaAboveLeaf1000230200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002302)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002302)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002302)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002302)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002302)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002302)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002302)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002302)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002302)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002302)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002302)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002302)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002302)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002302)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002302)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002302)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002302))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002302)) h
theorem e24KC2ThetaAboveLeaf1000230300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002303)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002303)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002303)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002303)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002303)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002303)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002303)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002303)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002303)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002303)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002303)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002303)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002303)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002303)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002303)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf1000230333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002303)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002303))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002303)) h
theorem e24KC2ThetaAboveLeaf100023100 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002310) = true := by
  have h : ((childLL thetaAboveCell10002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002310) h
theorem e24KC2ThetaAboveLeaf100023101 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002310) = true := by
  have h : ((childLH thetaAboveCell10002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002310) h
theorem e24KC2ThetaAboveLeaf100023102 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002310) = true := by
  have h : ((childHL thetaAboveCell10002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002310) h
theorem e24KC2ThetaAboveLeaf100023103 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002310) = true := by
  have h : ((childHH thetaAboveCell10002310)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002310) h
theorem e24KC2ThetaAboveLeaf100023110 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002311) = true := by
  have h : ((childLL thetaAboveCell10002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002311) h
theorem e24KC2ThetaAboveLeaf100023111 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002311) = true := by
  have h : ((childLH thetaAboveCell10002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002311) h
theorem e24KC2ThetaAboveLeaf100023112 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002311) = true := by
  have h : ((childHL thetaAboveCell10002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002311) h
theorem e24KC2ThetaAboveLeaf100023113 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002311) = true := by
  have h : ((childHH thetaAboveCell10002311)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002311) h
theorem e24KC2ThetaAboveLeaf1000231200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002312)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002312)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002312)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002312)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002312)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002312)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002312)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002312)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002312)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002312)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231222 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002312)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231223 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002312)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231230 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002312)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231231 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002312)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231232 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002312)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231233 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002312)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002312))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002312)) h
theorem e24KC2ThetaAboveLeaf1000231300 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10002313)) = true := by
  have h : ((childLL (childLL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231301 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10002313)) = true := by
  have h : ((childLH (childLL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231302 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10002313)) = true := by
  have h : ((childHL (childLL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231303 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10002313)) = true := by
  have h : ((childHH (childLL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231310 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10002313)) = true := by
  have h : ((childLL (childLH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231311 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10002313)) = true := by
  have h : ((childLH (childLH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231312 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10002313)) = true := by
  have h : ((childHL (childLH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231313 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10002313)) = true := by
  have h : ((childHH (childLH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231320 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10002313)) = true := by
  have h : ((childLL (childHL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231321 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10002313)) = true := by
  have h : ((childLH (childHL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231322 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell10002313)) = true := by
  have h : ((childHL (childHL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231323 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell10002313)) = true := by
  have h : ((childHH (childHL thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHL thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231330 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell10002313)) = true := by
  have h : ((childLL (childHH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231331 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell10002313)) = true := by
  have h : ((childLH (childHH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231332 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell10002313)) = true := by
  have h : ((childHL (childHH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childHH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf1000231333 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell10002313)) = true := by
  have h : ((childHH (childHH thetaAboveCell10002313))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childHH thetaAboveCell10002313)) h
theorem e24KC2ThetaAboveLeaf100023200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002320) = true := by
  have h : ((childLL thetaAboveCell10002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002320) h
theorem e24KC2ThetaAboveLeaf100023201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002320) = true := by
  have h : ((childLH thetaAboveCell10002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002320) h
theorem e24KC2ThetaAboveLeaf100023202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002320) = true := by
  have h : ((childHL thetaAboveCell10002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002320) h
theorem e24KC2ThetaAboveLeaf100023203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002320) = true := by
  have h : ((childHH thetaAboveCell10002320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002320) h
theorem e24KC2ThetaAboveLeaf100023210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002321) = true := by
  have h : ((childLL thetaAboveCell10002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002321) h
theorem e24KC2ThetaAboveLeaf100023211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002321) = true := by
  have h : ((childLH thetaAboveCell10002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002321) h
theorem e24KC2ThetaAboveLeaf100023212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002321) = true := by
  have h : ((childHL thetaAboveCell10002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002321) h
theorem e24KC2ThetaAboveLeaf100023213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002321) = true := by
  have h : ((childHH thetaAboveCell10002321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002321) h
theorem e24KC2ThetaAboveLeaf10002322 :
    adaptiveCoverCheck 11 thetaAboveCell10002322 = true := by
  have h : (thetaAboveCell10002322).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002322 h
theorem e24KC2ThetaAboveLeaf10002323 :
    adaptiveCoverCheck 11 thetaAboveCell10002323 = true := by
  have h : (thetaAboveCell10002323).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002323 h
theorem e24KC2ThetaAboveLeaf100023300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002330) = true := by
  have h : ((childLL thetaAboveCell10002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002330) h
theorem e24KC2ThetaAboveLeaf100023301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002330) = true := by
  have h : ((childLH thetaAboveCell10002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002330) h
theorem e24KC2ThetaAboveLeaf100023302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002330) = true := by
  have h : ((childHL thetaAboveCell10002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002330) h
theorem e24KC2ThetaAboveLeaf100023303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002330) = true := by
  have h : ((childHH thetaAboveCell10002330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002330) h
theorem e24KC2ThetaAboveLeaf100023310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10002331) = true := by
  have h : ((childLL thetaAboveCell10002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10002331) h
theorem e24KC2ThetaAboveLeaf100023311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10002331) = true := by
  have h : ((childLH thetaAboveCell10002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10002331) h
theorem e24KC2ThetaAboveLeaf100023312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10002331) = true := by
  have h : ((childHL thetaAboveCell10002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10002331) h
theorem e24KC2ThetaAboveLeaf100023313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10002331) = true := by
  have h : ((childHH thetaAboveCell10002331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10002331) h
theorem e24KC2ThetaAboveLeaf10002332 :
    adaptiveCoverCheck 11 thetaAboveCell10002332 = true := by
  have h : (thetaAboveCell10002332).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002332 h
theorem e24KC2ThetaAboveLeaf10002333 :
    adaptiveCoverCheck 11 thetaAboveCell10002333 = true := by
  have h : (thetaAboveCell10002333).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10002333 h
theorem e24KC2ThetaAboveLeaf1000300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1000))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf1000301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1000))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf10003020 :
    adaptiveCoverCheck 11 thetaAboveCell10003020 = true := by
  have h : (thetaAboveCell10003020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003020 h
theorem e24KC2ThetaAboveLeaf10003021 :
    adaptiveCoverCheck 11 thetaAboveCell10003021 = true := by
  have h : (thetaAboveCell10003021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003021 h
theorem e24KC2ThetaAboveLeaf10003022 :
    adaptiveCoverCheck 11 thetaAboveCell10003022 = true := by
  have h : (thetaAboveCell10003022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003022 h
theorem e24KC2ThetaAboveLeaf10003023 :
    adaptiveCoverCheck 11 thetaAboveCell10003023 = true := by
  have h : (thetaAboveCell10003023).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003023 h
theorem e24KC2ThetaAboveLeaf10003030 :
    adaptiveCoverCheck 11 thetaAboveCell10003030 = true := by
  have h : (thetaAboveCell10003030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003030 h
theorem e24KC2ThetaAboveLeaf10003031 :
    adaptiveCoverCheck 11 thetaAboveCell10003031 = true := by
  have h : (thetaAboveCell10003031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003031 h
theorem e24KC2ThetaAboveLeaf10003032 :
    adaptiveCoverCheck 11 thetaAboveCell10003032 = true := by
  have h : (thetaAboveCell10003032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003032 h
theorem e24KC2ThetaAboveLeaf10003033 :
    adaptiveCoverCheck 11 thetaAboveCell10003033 = true := by
  have h : (thetaAboveCell10003033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003033 h
theorem e24KC2ThetaAboveLeaf1000310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1000))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf1000311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1000))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1000)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1000))) h
theorem e24KC2ThetaAboveLeaf10003120 :
    adaptiveCoverCheck 11 thetaAboveCell10003120 = true := by
  have h : (thetaAboveCell10003120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003120 h
theorem e24KC2ThetaAboveLeaf10003121 :
    adaptiveCoverCheck 11 thetaAboveCell10003121 = true := by
  have h : (thetaAboveCell10003121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003121 h
theorem e24KC2ThetaAboveLeaf10003122 :
    adaptiveCoverCheck 11 thetaAboveCell10003122 = true := by
  have h : (thetaAboveCell10003122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003122 h
theorem e24KC2ThetaAboveLeaf10003123 :
    adaptiveCoverCheck 11 thetaAboveCell10003123 = true := by
  have h : (thetaAboveCell10003123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003123 h
theorem e24KC2ThetaAboveLeaf10003130 :
    adaptiveCoverCheck 11 thetaAboveCell10003130 = true := by
  have h : (thetaAboveCell10003130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003130 h
theorem e24KC2ThetaAboveLeaf10003131 :
    adaptiveCoverCheck 11 thetaAboveCell10003131 = true := by
  have h : (thetaAboveCell10003131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003131 h
theorem e24KC2ThetaAboveLeaf10003132 :
    adaptiveCoverCheck 11 thetaAboveCell10003132 = true := by
  have h : (thetaAboveCell10003132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003132 h
theorem e24KC2ThetaAboveLeaf10003133 :
    adaptiveCoverCheck 11 thetaAboveCell10003133 = true := by
  have h : (thetaAboveCell10003133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell10003133 h
theorem e24KC2ThetaAboveLeaf100032000 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003200) = true := by
  have h : ((childLL thetaAboveCell10003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003200) h
theorem e24KC2ThetaAboveLeaf100032001 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003200) = true := by
  have h : ((childLH thetaAboveCell10003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003200) h
theorem e24KC2ThetaAboveLeaf100032002 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003200) = true := by
  have h : ((childHL thetaAboveCell10003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003200) h
theorem e24KC2ThetaAboveLeaf100032003 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003200) = true := by
  have h : ((childHH thetaAboveCell10003200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003200) h
theorem e24KC2ThetaAboveLeaf100032010 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell10003201) = true := by
  have h : ((childLL thetaAboveCell10003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell10003201) h
theorem e24KC2ThetaAboveLeaf100032011 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell10003201) = true := by
  have h : ((childLH thetaAboveCell10003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell10003201) h
theorem e24KC2ThetaAboveLeaf100032012 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell10003201) = true := by
  have h : ((childHL thetaAboveCell10003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell10003201) h
theorem e24KC2ThetaAboveLeaf100032013 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell10003201) = true := by
  have h : ((childHH thetaAboveCell10003201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell10003201) h
theorem e24KC2ThetaAboveLeaf1000320200 :
    adaptiveCoverCheck 9 (childLL (childLL thetaAboveCell10003202)) = true := by
  have h : ((childLL (childLL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320201 :
    adaptiveCoverCheck 9 (childLH (childLL thetaAboveCell10003202)) = true := by
  have h : ((childLH (childLL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320202 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell10003202)) = true := by
  have h : ((childHL (childLL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320203 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell10003202)) = true := by
  have h : ((childHH (childLL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320210 :
    adaptiveCoverCheck 9 (childLL (childLH thetaAboveCell10003202)) = true := by
  have h : ((childLL (childLH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childLH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320211 :
    adaptiveCoverCheck 9 (childLH (childLH thetaAboveCell10003202)) = true := by
  have h : ((childLH (childLH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childLH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320212 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell10003202)) = true := by
  have h : ((childHL (childLH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL (childLH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320213 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell10003202)) = true := by
  have h : ((childHH (childLH thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH (childLH thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320220 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell10003202)) = true := by
  have h : ((childLL (childHL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL thetaAboveCell10003202)) h
theorem e24KC2ThetaAboveLeaf1000320221 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell10003202)) = true := by
  have h : ((childLH (childHL thetaAboveCell10003202))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH (childHL thetaAboveCell10003202)) h

end PartE
end GerverSofa

end

end

end

end

end

end

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchDeeff549d6afce41`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7b7ba6d809

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells7b7ba6d809

open CertificateCells7b7ba6d809
theorem cover_subtree_7c323abdd313 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012000
        (by
          have h : ((childLL thetaAboveCell000032012000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012000) h)
        (by
          have h : ((childLH thetaAboveCell000032012000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012000) h)
        (by
          have h : ((childHL thetaAboveCell000032012000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012000) h)
        (by
          have h : ((childHH thetaAboveCell000032012000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012001
        (by
          have h : ((childLL thetaAboveCell000032012001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012001) h)
        (by
          have h : ((childLH thetaAboveCell000032012001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012001) h)
        (by
          have h : ((childHL thetaAboveCell000032012001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012001) h)
        (by
          have h : ((childHH thetaAboveCell000032012001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012001) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012002
        (by
          have h : ((childLL thetaAboveCell000032012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012002) h)
        (by
          have h : ((childLH thetaAboveCell000032012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012002) h)
        (by
          have h : ((childHL thetaAboveCell000032012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012002) h)
        (by
          have h : ((childHH thetaAboveCell000032012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012003
        (by
          have h : ((childLL thetaAboveCell000032012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012003) h)
        (by
          have h : ((childLH thetaAboveCell000032012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012003) h)
        (by
          have h : ((childHL thetaAboveCell000032012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012003) h)
        (by
          have h : ((childHH thetaAboveCell000032012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012003) h))

theorem cover_subtree_2c6010c13cb7 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012010
        (by
          have h : ((childLL thetaAboveCell000032012010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012010) h)
        (by
          have h : ((childLH thetaAboveCell000032012010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012010) h)
        (by
          have h : ((childHL thetaAboveCell000032012010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012010) h)
        (by
          have h : ((childHH thetaAboveCell000032012010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012011
        (by
          have h : ((childLL thetaAboveCell000032012011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012011) h)
        (by
          have h : ((childLH thetaAboveCell000032012011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012011) h)
        (by
          have h : ((childHL thetaAboveCell000032012011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012011) h)
        (by
          have h : ((childHH thetaAboveCell000032012011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012011) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012012
        (by
          have h : ((childLL thetaAboveCell000032012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012012) h)
        (by
          have h : ((childLH thetaAboveCell000032012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012012) h)
        (by
          have h : ((childHL thetaAboveCell000032012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012012) h)
        (by
          have h : ((childHH thetaAboveCell000032012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012013
        (by
          have h : ((childLL thetaAboveCell000032012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012013) h)
        (by
          have h : ((childLH thetaAboveCell000032012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012013) h)
        (by
          have h : ((childHL thetaAboveCell000032012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012013) h)
        (by
          have h : ((childHH thetaAboveCell000032012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012013) h))

theorem cover_subtree_1c36f4e287e2 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012020
        (by
          have h : ((childLL thetaAboveCell000032012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012020) h)
        (by
          have h : ((childLH thetaAboveCell000032012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012020) h)
        (by
          have h : ((childHL thetaAboveCell000032012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012020) h)
        (by
          have h : ((childHH thetaAboveCell000032012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012021
        (by
          have h : ((childLL thetaAboveCell000032012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012021) h)
        (by
          have h : ((childLH thetaAboveCell000032012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012021) h)
        (by
          have h : ((childHL thetaAboveCell000032012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012021) h)
        (by
          have h : ((childHH thetaAboveCell000032012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012021) h))
    (by
      have h : (thetaAboveCell000032012022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012022 h)
    (by
      have h : (thetaAboveCell000032012023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012023 h)

theorem cover_subtree_2d88b84be921 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012030
        (by
          have h : ((childLL thetaAboveCell000032012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012030) h)
        (by
          have h : ((childLH thetaAboveCell000032012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012030) h)
        (by
          have h : ((childHL thetaAboveCell000032012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012030) h)
        (by
          have h : ((childHH thetaAboveCell000032012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012031
        (by
          have h : ((childLL thetaAboveCell000032012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012031) h)
        (by
          have h : ((childLH thetaAboveCell000032012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012031) h)
        (by
          have h : ((childHL thetaAboveCell000032012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012031) h)
        (by
          have h : ((childHH thetaAboveCell000032012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012031) h))
    (by
      have h : (thetaAboveCell000032012032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012032 h)
    (by
      have h : (thetaAboveCell000032012033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012033 h)

theorem e24KC2ThetaAboveLeaf0000320120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003201))
    cover_subtree_7c323abdd313
    cover_subtree_2c6010c13cb7
    cover_subtree_1c36f4e287e2
    cover_subtree_2d88b84be921
theorem cover_subtree_15ce3b085062 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012100
        (by
          have h : ((childLL thetaAboveCell000032012100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012100) h)
        (by
          have h : ((childLH thetaAboveCell000032012100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012100) h)
        (by
          have h : ((childHL thetaAboveCell000032012100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012100) h)
        (by
          have h : ((childHH thetaAboveCell000032012100)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012100) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012101
        (by
          have h : ((childLL thetaAboveCell000032012101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012101) h)
        (by
          have h : ((childLH thetaAboveCell000032012101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012101) h)
        (by
          have h : ((childHL thetaAboveCell000032012101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012101) h)
        (by
          have h : ((childHH thetaAboveCell000032012101)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012101) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012102
        (by
          have h : ((childLL thetaAboveCell000032012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012102) h)
        (by
          have h : ((childLH thetaAboveCell000032012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012102) h)
        (by
          have h : ((childHL thetaAboveCell000032012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012102) h)
        (by
          have h : ((childHH thetaAboveCell000032012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012103
        (by
          have h : ((childLL thetaAboveCell000032012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012103) h)
        (by
          have h : ((childLH thetaAboveCell000032012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012103) h)
        (by
          have h : ((childHL thetaAboveCell000032012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012103) h)
        (by
          have h : ((childHH thetaAboveCell000032012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012103) h))

theorem cover_subtree_08caed552cac :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012110
        (by
          have h : ((childLL thetaAboveCell000032012110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012110) h)
        (by
          have h : ((childLH thetaAboveCell000032012110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012110) h)
        (by
          have h : ((childHL thetaAboveCell000032012110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012110) h)
        (by
          have h : ((childHH thetaAboveCell000032012110)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012110) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012111
        (by
          have h : ((childLL thetaAboveCell000032012111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012111) h)
        (by
          have h : ((childLH thetaAboveCell000032012111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012111) h)
        (by
          have h : ((childHL thetaAboveCell000032012111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012111) h)
        (by
          have h : ((childHH thetaAboveCell000032012111)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012111) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012112
        (by
          have h : ((childLL thetaAboveCell000032012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012112) h)
        (by
          have h : ((childLH thetaAboveCell000032012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012112) h)
        (by
          have h : ((childHL thetaAboveCell000032012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012112) h)
        (by
          have h : ((childHH thetaAboveCell000032012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012113
        (by
          have h : ((childLL thetaAboveCell000032012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012113) h)
        (by
          have h : ((childLH thetaAboveCell000032012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012113) h)
        (by
          have h : ((childHL thetaAboveCell000032012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012113) h)
        (by
          have h : ((childHH thetaAboveCell000032012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012113) h))

theorem cover_subtree_26481d0c715c :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012120
        (by
          have h : ((childLL thetaAboveCell000032012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012120) h)
        (by
          have h : ((childLH thetaAboveCell000032012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012120) h)
        (by
          have h : ((childHL thetaAboveCell000032012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012120) h)
        (by
          have h : ((childHH thetaAboveCell000032012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012121
        (by
          have h : ((childLL thetaAboveCell000032012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012121) h)
        (by
          have h : ((childLH thetaAboveCell000032012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012121) h)
        (by
          have h : ((childHL thetaAboveCell000032012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012121) h)
        (by
          have h : ((childHH thetaAboveCell000032012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012121) h))
    (by
      have h : (thetaAboveCell000032012122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012122 h)
    (by
      have h : (thetaAboveCell000032012123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012123 h)

theorem cover_subtree_a0f2894108e0 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012130
        (by
          have h : ((childLL thetaAboveCell000032012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012130) h)
        (by
          have h : ((childLH thetaAboveCell000032012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012130) h)
        (by
          have h : ((childHL thetaAboveCell000032012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012130) h)
        (by
          have h : ((childHH thetaAboveCell000032012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032012131
        (by
          have h : ((childLL thetaAboveCell000032012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032012131) h)
        (by
          have h : ((childLH thetaAboveCell000032012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032012131) h)
        (by
          have h : ((childHL thetaAboveCell000032012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032012131) h)
        (by
          have h : ((childHH thetaAboveCell000032012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032012131) h))
    (by
      have h : (thetaAboveCell000032012132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012132 h)
    (by
      have h : (thetaAboveCell000032012133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032012133 h)

theorem e24KC2ThetaAboveLeaf0000320121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003201))
    cover_subtree_15ce3b085062
    cover_subtree_08caed552cac
    cover_subtree_26481d0c715c
    cover_subtree_a0f2894108e0
theorem e24KC2ThetaAboveLeaf0000320122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003201))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003201))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003201))) h)
theorem cover_subtree_69db60e02bff :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013000
        (by
          have h : ((childLL thetaAboveCell000032013000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013000) h)
        (by
          have h : ((childLH thetaAboveCell000032013000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013000) h)
        (by
          have h : ((childHL thetaAboveCell000032013000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013000) h)
        (by
          have h : ((childHH thetaAboveCell000032013000)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013000) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013001
        (by
          have h : ((childLL thetaAboveCell000032013001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013001) h)
        (by
          have h : ((childLH thetaAboveCell000032013001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013001) h)
        (by
          have h : ((childHL thetaAboveCell000032013001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013001) h)
        (by
          have h : ((childHH thetaAboveCell000032013001)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013001) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013002
        (by
          have h : ((childLL thetaAboveCell000032013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013002) h)
        (by
          have h : ((childLH thetaAboveCell000032013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013002) h)
        (by
          have h : ((childHL thetaAboveCell000032013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013002) h)
        (by
          have h : ((childHH thetaAboveCell000032013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013003
        (by
          have h : ((childLL thetaAboveCell000032013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013003) h)
        (by
          have h : ((childLH thetaAboveCell000032013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013003) h)
        (by
          have h : ((childHL thetaAboveCell000032013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013003) h)
        (by
          have h : ((childHH thetaAboveCell000032013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013003) h))

theorem cover_subtree_42fb80f99488 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013010
        (by
          have h : ((childLL thetaAboveCell000032013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013010) h)
        (by
          have h : ((childLH thetaAboveCell000032013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013010) h)
        (by
          have h : ((childHL thetaAboveCell000032013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013010) h)
        (by
          have h : ((childHH thetaAboveCell000032013010)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013010) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013011
        (by
          have h : ((childLL thetaAboveCell000032013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013011) h)
        (by
          have h : ((childLH thetaAboveCell000032013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013011) h)
        (by
          have h : ((childHL thetaAboveCell000032013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013011) h)
        (by
          have h : ((childHH thetaAboveCell000032013011)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013011) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013012
        (by
          have h : ((childLL thetaAboveCell000032013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013012) h)
        (by
          have h : ((childLH thetaAboveCell000032013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013012) h)
        (by
          have h : ((childHL thetaAboveCell000032013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013012) h)
        (by
          have h : ((childHH thetaAboveCell000032013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013013
        (by
          have h : ((childLL thetaAboveCell000032013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013013) h)
        (by
          have h : ((childLH thetaAboveCell000032013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013013) h)
        (by
          have h : ((childHL thetaAboveCell000032013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013013) h)
        (by
          have h : ((childHH thetaAboveCell000032013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013013) h))

theorem cover_subtree_190c09664a4f :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013020
        (by
          have h : ((childLL thetaAboveCell000032013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013020) h)
        (by
          have h : ((childLH thetaAboveCell000032013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013020) h)
        (by
          have h : ((childHL thetaAboveCell000032013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013020) h)
        (by
          have h : ((childHH thetaAboveCell000032013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013021
        (by
          have h : ((childLL thetaAboveCell000032013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013021) h)
        (by
          have h : ((childLH thetaAboveCell000032013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013021) h)
        (by
          have h : ((childHL thetaAboveCell000032013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013021) h)
        (by
          have h : ((childHH thetaAboveCell000032013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013021) h))
    (by
      have h : (thetaAboveCell000032013022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013022 h)
    (by
      have h : (thetaAboveCell000032013023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013023 h)

theorem cover_subtree_f68e71dd24e5 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013030
        (by
          have h : ((childLL thetaAboveCell000032013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013030) h)
        (by
          have h : ((childLH thetaAboveCell000032013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013030) h)
        (by
          have h : ((childHL thetaAboveCell000032013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013030) h)
        (by
          have h : ((childHH thetaAboveCell000032013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013031
        (by
          have h : ((childLL thetaAboveCell000032013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013031) h)
        (by
          have h : ((childLH thetaAboveCell000032013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013031) h)
        (by
          have h : ((childHL thetaAboveCell000032013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013031) h)
        (by
          have h : ((childHH thetaAboveCell000032013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013031) h))
    (by
      have h : (thetaAboveCell000032013032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013032 h)
    (by
      have h : (thetaAboveCell000032013033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013033 h)

theorem e24KC2ThetaAboveLeaf0000320130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003201))
    cover_subtree_69db60e02bff
    cover_subtree_42fb80f99488
    cover_subtree_190c09664a4f
    cover_subtree_f68e71dd24e5
theorem cover_subtree_7cb6ec704eae :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003201)))
    (by
      have h : (thetaAboveCell000032013100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013100 h)
    (by
      have h : (thetaAboveCell000032013101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013102
        (by
          have h : ((childLL thetaAboveCell000032013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013102) h)
        (by
          have h : ((childLH thetaAboveCell000032013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013102) h)
        (by
          have h : ((childHL thetaAboveCell000032013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013102) h)
        (by
          have h : ((childHH thetaAboveCell000032013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013103
        (by
          have h : ((childLL thetaAboveCell000032013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013103) h)
        (by
          have h : ((childLH thetaAboveCell000032013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013103) h)
        (by
          have h : ((childHL thetaAboveCell000032013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013103) h)
        (by
          have h : ((childHH thetaAboveCell000032013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013103) h))

theorem cover_subtree_5ed05ff39522 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003201)))
    (by
      have h : (thetaAboveCell000032013110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013110 h)
    (by
      have h : (thetaAboveCell000032013111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013112
        (by
          have h : ((childLL thetaAboveCell000032013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013112) h)
        (by
          have h : ((childLH thetaAboveCell000032013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013112) h)
        (by
          have h : ((childHL thetaAboveCell000032013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013112) h)
        (by
          have h : ((childHH thetaAboveCell000032013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013113
        (by
          have h : ((childLL thetaAboveCell000032013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013113) h)
        (by
          have h : ((childLH thetaAboveCell000032013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013113) h)
        (by
          have h : ((childHL thetaAboveCell000032013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013113) h)
        (by
          have h : ((childHH thetaAboveCell000032013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013113) h))

theorem cover_subtree_0c55724b42aa :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013120
        (by
          have h : ((childLL thetaAboveCell000032013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013120) h)
        (by
          have h : ((childLH thetaAboveCell000032013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013120) h)
        (by
          have h : ((childHL thetaAboveCell000032013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013120) h)
        (by
          have h : ((childHH thetaAboveCell000032013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013121
        (by
          have h : ((childLL thetaAboveCell000032013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013121) h)
        (by
          have h : ((childLH thetaAboveCell000032013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013121) h)
        (by
          have h : ((childHL thetaAboveCell000032013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013121) h)
        (by
          have h : ((childHH thetaAboveCell000032013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013121) h))
    (by
      have h : (thetaAboveCell000032013122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013122 h)
    (by
      have h : (thetaAboveCell000032013123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013123 h)

theorem cover_subtree_a20be064bbc9 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003201)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013130
        (by
          have h : ((childLL thetaAboveCell000032013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013130) h)
        (by
          have h : ((childLH thetaAboveCell000032013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013130) h)
        (by
          have h : ((childHL thetaAboveCell000032013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013130) h)
        (by
          have h : ((childHH thetaAboveCell000032013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032013131
        (by
          have h : ((childLL thetaAboveCell000032013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032013131) h)
        (by
          have h : ((childLH thetaAboveCell000032013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032013131) h)
        (by
          have h : ((childHL thetaAboveCell000032013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032013131) h)
        (by
          have h : ((childHH thetaAboveCell000032013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032013131) h))
    (by
      have h : (thetaAboveCell000032013132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013132 h)
    (by
      have h : (thetaAboveCell000032013133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032013133 h)

theorem e24KC2ThetaAboveLeaf0000320131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003201))
    cover_subtree_7cb6ec704eae
    cover_subtree_5ed05ff39522
    cover_subtree_0c55724b42aa
    cover_subtree_a20be064bbc9
theorem e24KC2ThetaAboveLeaf0000320132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003201))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000320133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003201))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003201))) h)
theorem e24KC2ThetaAboveLeaf0000321002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003210))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003210))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003210))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003210))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003210))) h)
theorem cover_subtree_0ba391c6ec0d :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032102000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102000 h)
    (by
      have h : (thetaAboveCell000032102001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102002
        (by
          have h : ((childLL thetaAboveCell000032102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102002) h)
        (by
          have h : ((childLH thetaAboveCell000032102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102002) h)
        (by
          have h : ((childHL thetaAboveCell000032102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102002) h)
        (by
          have h : ((childHH thetaAboveCell000032102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102003
        (by
          have h : ((childLL thetaAboveCell000032102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102003) h)
        (by
          have h : ((childLH thetaAboveCell000032102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102003) h)
        (by
          have h : ((childHL thetaAboveCell000032102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102003) h)
        (by
          have h : ((childHH thetaAboveCell000032102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102003) h))

theorem cover_subtree_8fafa3f6224a :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032102010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102010 h)
    (by
      have h : (thetaAboveCell000032102011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102012
        (by
          have h : ((childLL thetaAboveCell000032102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102012) h)
        (by
          have h : ((childLH thetaAboveCell000032102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102012) h)
        (by
          have h : ((childHL thetaAboveCell000032102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102012) h)
        (by
          have h : ((childHH thetaAboveCell000032102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102013
        (by
          have h : ((childLL thetaAboveCell000032102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102013) h)
        (by
          have h : ((childLH thetaAboveCell000032102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102013) h)
        (by
          have h : ((childHL thetaAboveCell000032102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102013) h)
        (by
          have h : ((childHH thetaAboveCell000032102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102013) h))

theorem cover_subtree_d5e7f8726976 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102020
        (by
          have h : ((childLL thetaAboveCell000032102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102020) h)
        (by
          have h : ((childLH thetaAboveCell000032102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102020) h)
        (by
          have h : ((childHL thetaAboveCell000032102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102020) h)
        (by
          have h : ((childHH thetaAboveCell000032102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102021
        (by
          have h : ((childLL thetaAboveCell000032102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102021) h)
        (by
          have h : ((childLH thetaAboveCell000032102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102021) h)
        (by
          have h : ((childHL thetaAboveCell000032102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102021) h)
        (by
          have h : ((childHH thetaAboveCell000032102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102021) h))
    (by
      have h : (thetaAboveCell000032102022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102022 h)
    (by
      have h : (thetaAboveCell000032102023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102023 h)

theorem cover_subtree_c2e91aa19513 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102030
        (by
          have h : ((childLL thetaAboveCell000032102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102030) h)
        (by
          have h : ((childLH thetaAboveCell000032102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102030) h)
        (by
          have h : ((childHL thetaAboveCell000032102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102030) h)
        (by
          have h : ((childHH thetaAboveCell000032102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102031
        (by
          have h : ((childLL thetaAboveCell000032102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102031) h)
        (by
          have h : ((childLH thetaAboveCell000032102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102031) h)
        (by
          have h : ((childHL thetaAboveCell000032102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102031) h)
        (by
          have h : ((childHH thetaAboveCell000032102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102031) h))
    (by
      have h : (thetaAboveCell000032102032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102032 h)
    (by
      have h : (thetaAboveCell000032102033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102033 h)

theorem e24KC2ThetaAboveLeaf0000321020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003210))
    cover_subtree_0ba391c6ec0d
    cover_subtree_8fafa3f6224a
    cover_subtree_d5e7f8726976
    cover_subtree_c2e91aa19513
theorem cover_subtree_80cc442a7cb0 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032102100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102100 h)
    (by
      have h : (thetaAboveCell000032102101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102102
        (by
          have h : ((childLL thetaAboveCell000032102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102102) h)
        (by
          have h : ((childLH thetaAboveCell000032102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102102) h)
        (by
          have h : ((childHL thetaAboveCell000032102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102102) h)
        (by
          have h : ((childHH thetaAboveCell000032102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102103
        (by
          have h : ((childLL thetaAboveCell000032102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102103) h)
        (by
          have h : ((childLH thetaAboveCell000032102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102103) h)
        (by
          have h : ((childHL thetaAboveCell000032102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102103) h)
        (by
          have h : ((childHH thetaAboveCell000032102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102103) h))

theorem cover_subtree_7d2d9f5abf21 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032102110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102110 h)
    (by
      have h : (thetaAboveCell000032102111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102112
        (by
          have h : ((childLL thetaAboveCell000032102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102112) h)
        (by
          have h : ((childLH thetaAboveCell000032102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102112) h)
        (by
          have h : ((childHL thetaAboveCell000032102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102112) h)
        (by
          have h : ((childHH thetaAboveCell000032102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102113
        (by
          have h : ((childLL thetaAboveCell000032102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102113) h)
        (by
          have h : ((childLH thetaAboveCell000032102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102113) h)
        (by
          have h : ((childHL thetaAboveCell000032102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102113) h)
        (by
          have h : ((childHH thetaAboveCell000032102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102113) h))

theorem cover_subtree_4430ea3984ba :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102120
        (by
          have h : ((childLL thetaAboveCell000032102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102120) h)
        (by
          have h : ((childLH thetaAboveCell000032102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102120) h)
        (by
          have h : ((childHL thetaAboveCell000032102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102120) h)
        (by
          have h : ((childHH thetaAboveCell000032102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102121
        (by
          have h : ((childLL thetaAboveCell000032102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102121) h)
        (by
          have h : ((childLH thetaAboveCell000032102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102121) h)
        (by
          have h : ((childHL thetaAboveCell000032102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102121) h)
        (by
          have h : ((childHH thetaAboveCell000032102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102121) h))
    (by
      have h : (thetaAboveCell000032102122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102122 h)
    (by
      have h : (thetaAboveCell000032102123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102123 h)

theorem cover_subtree_7e0429da25bc :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102130
        (by
          have h : ((childLL thetaAboveCell000032102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102130) h)
        (by
          have h : ((childLH thetaAboveCell000032102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102130) h)
        (by
          have h : ((childHL thetaAboveCell000032102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102130) h)
        (by
          have h : ((childHH thetaAboveCell000032102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032102131
        (by
          have h : ((childLL thetaAboveCell000032102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032102131) h)
        (by
          have h : ((childLH thetaAboveCell000032102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032102131) h)
        (by
          have h : ((childHL thetaAboveCell000032102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032102131) h)
        (by
          have h : ((childHH thetaAboveCell000032102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032102131) h))
    (by
      have h : (thetaAboveCell000032102132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102132 h)
    (by
      have h : (thetaAboveCell000032102133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032102133 h)

theorem e24KC2ThetaAboveLeaf0000321021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003210))
    cover_subtree_80cc442a7cb0
    cover_subtree_7d2d9f5abf21
    cover_subtree_4430ea3984ba
    cover_subtree_7e0429da25bc
theorem e24KC2ThetaAboveLeaf0000321022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003210))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003210))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003210))) h)
theorem cover_subtree_c3fcf1053462 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032103000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103000 h)
    (by
      have h : (thetaAboveCell000032103001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103002
        (by
          have h : ((childLL thetaAboveCell000032103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103002) h)
        (by
          have h : ((childLH thetaAboveCell000032103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103002) h)
        (by
          have h : ((childHL thetaAboveCell000032103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103002) h)
        (by
          have h : ((childHH thetaAboveCell000032103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103003
        (by
          have h : ((childLL thetaAboveCell000032103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103003) h)
        (by
          have h : ((childLH thetaAboveCell000032103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103003) h)
        (by
          have h : ((childHL thetaAboveCell000032103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103003) h)
        (by
          have h : ((childHH thetaAboveCell000032103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103003) h))

theorem cover_subtree_c50e8ae52b0f :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032103010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103010 h)
    (by
      have h : (thetaAboveCell000032103011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103012
        (by
          have h : ((childLL thetaAboveCell000032103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103012) h)
        (by
          have h : ((childLH thetaAboveCell000032103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103012) h)
        (by
          have h : ((childHL thetaAboveCell000032103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103012) h)
        (by
          have h : ((childHH thetaAboveCell000032103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103013
        (by
          have h : ((childLL thetaAboveCell000032103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103013) h)
        (by
          have h : ((childLH thetaAboveCell000032103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103013) h)
        (by
          have h : ((childHL thetaAboveCell000032103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103013) h)
        (by
          have h : ((childHH thetaAboveCell000032103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103013) h))

theorem cover_subtree_d417fd422e6e :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103020
        (by
          have h : ((childLL thetaAboveCell000032103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103020) h)
        (by
          have h : ((childLH thetaAboveCell000032103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103020) h)
        (by
          have h : ((childHL thetaAboveCell000032103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103020) h)
        (by
          have h : ((childHH thetaAboveCell000032103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103021
        (by
          have h : ((childLL thetaAboveCell000032103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103021) h)
        (by
          have h : ((childLH thetaAboveCell000032103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103021) h)
        (by
          have h : ((childHL thetaAboveCell000032103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103021) h)
        (by
          have h : ((childHH thetaAboveCell000032103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103021) h))
    (by
      have h : (thetaAboveCell000032103022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103022 h)
    (by
      have h : (thetaAboveCell000032103023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103023 h)

theorem cover_subtree_803a1ba0f62b :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103030
        (by
          have h : ((childLL thetaAboveCell000032103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103030) h)
        (by
          have h : ((childLH thetaAboveCell000032103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103030) h)
        (by
          have h : ((childHL thetaAboveCell000032103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103030) h)
        (by
          have h : ((childHH thetaAboveCell000032103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103031
        (by
          have h : ((childLL thetaAboveCell000032103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103031) h)
        (by
          have h : ((childLH thetaAboveCell000032103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103031) h)
        (by
          have h : ((childHL thetaAboveCell000032103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103031) h)
        (by
          have h : ((childHH thetaAboveCell000032103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103031) h))
    (by
      have h : (thetaAboveCell000032103032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103032 h)
    (by
      have h : (thetaAboveCell000032103033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103033 h)

theorem e24KC2ThetaAboveLeaf0000321030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003210))
    cover_subtree_c3fcf1053462
    cover_subtree_c50e8ae52b0f
    cover_subtree_d417fd422e6e
    cover_subtree_803a1ba0f62b
theorem cover_subtree_dc9cc0fd25e0 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032103100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103100 h)
    (by
      have h : (thetaAboveCell000032103101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103102
        (by
          have h : ((childLL thetaAboveCell000032103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103102) h)
        (by
          have h : ((childLH thetaAboveCell000032103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103102) h)
        (by
          have h : ((childHL thetaAboveCell000032103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103102) h)
        (by
          have h : ((childHH thetaAboveCell000032103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103103
        (by
          have h : ((childLL thetaAboveCell000032103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103103) h)
        (by
          have h : ((childLH thetaAboveCell000032103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103103) h)
        (by
          have h : ((childHL thetaAboveCell000032103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103103) h)
        (by
          have h : ((childHH thetaAboveCell000032103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103103) h))

theorem cover_subtree_4e80a706fe6e :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003210)))
    (by
      have h : (thetaAboveCell000032103110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103110 h)
    (by
      have h : (thetaAboveCell000032103111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103112
        (by
          have h : ((childLL thetaAboveCell000032103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103112) h)
        (by
          have h : ((childLH thetaAboveCell000032103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103112) h)
        (by
          have h : ((childHL thetaAboveCell000032103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103112) h)
        (by
          have h : ((childHH thetaAboveCell000032103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103113
        (by
          have h : ((childLL thetaAboveCell000032103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103113) h)
        (by
          have h : ((childLH thetaAboveCell000032103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103113) h)
        (by
          have h : ((childHL thetaAboveCell000032103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103113) h)
        (by
          have h : ((childHH thetaAboveCell000032103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103113) h))

theorem cover_subtree_06156bdf5c57 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103120
        (by
          have h : ((childLL thetaAboveCell000032103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103120) h)
        (by
          have h : ((childLH thetaAboveCell000032103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103120) h)
        (by
          have h : ((childHL thetaAboveCell000032103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103120) h)
        (by
          have h : ((childHH thetaAboveCell000032103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103121
        (by
          have h : ((childLL thetaAboveCell000032103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103121) h)
        (by
          have h : ((childLH thetaAboveCell000032103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103121) h)
        (by
          have h : ((childHL thetaAboveCell000032103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103121) h)
        (by
          have h : ((childHH thetaAboveCell000032103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103121) h))
    (by
      have h : (thetaAboveCell000032103122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103122 h)
    (by
      have h : (thetaAboveCell000032103123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103123 h)

theorem cover_subtree_dfe1ff6f4f14 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003210)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103130
        (by
          have h : ((childLL thetaAboveCell000032103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103130) h)
        (by
          have h : ((childLH thetaAboveCell000032103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103130) h)
        (by
          have h : ((childHL thetaAboveCell000032103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103130) h)
        (by
          have h : ((childHH thetaAboveCell000032103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032103131
        (by
          have h : ((childLL thetaAboveCell000032103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032103131) h)
        (by
          have h : ((childLH thetaAboveCell000032103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032103131) h)
        (by
          have h : ((childHL thetaAboveCell000032103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032103131) h)
        (by
          have h : ((childHH thetaAboveCell000032103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032103131) h))
    (by
      have h : (thetaAboveCell000032103132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103132 h)
    (by
      have h : (thetaAboveCell000032103133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032103133 h)

theorem e24KC2ThetaAboveLeaf0000321031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003210))
    cover_subtree_dc9cc0fd25e0
    cover_subtree_4e80a706fe6e
    cover_subtree_06156bdf5c57
    cover_subtree_dfe1ff6f4f14
theorem e24KC2ThetaAboveLeaf0000321032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003210))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003210))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003210))) h)
theorem e24KC2ThetaAboveLeaf0000321102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003211))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003211))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003211))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003211))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003211))) h)
theorem cover_subtree_5921e16da435 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032112000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112000 h)
    (by
      have h : (thetaAboveCell000032112001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112002
        (by
          have h : ((childLL thetaAboveCell000032112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112002) h)
        (by
          have h : ((childLH thetaAboveCell000032112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112002) h)
        (by
          have h : ((childHL thetaAboveCell000032112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112002) h)
        (by
          have h : ((childHH thetaAboveCell000032112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112003
        (by
          have h : ((childLL thetaAboveCell000032112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112003) h)
        (by
          have h : ((childLH thetaAboveCell000032112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112003) h)
        (by
          have h : ((childHL thetaAboveCell000032112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112003) h)
        (by
          have h : ((childHH thetaAboveCell000032112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112003) h))

theorem cover_subtree_52f1b09bd9bd :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032112010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112010 h)
    (by
      have h : (thetaAboveCell000032112011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112012
        (by
          have h : ((childLL thetaAboveCell000032112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112012) h)
        (by
          have h : ((childLH thetaAboveCell000032112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112012) h)
        (by
          have h : ((childHL thetaAboveCell000032112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112012) h)
        (by
          have h : ((childHH thetaAboveCell000032112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112013
        (by
          have h : ((childLL thetaAboveCell000032112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112013) h)
        (by
          have h : ((childLH thetaAboveCell000032112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112013) h)
        (by
          have h : ((childHL thetaAboveCell000032112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112013) h)
        (by
          have h : ((childHH thetaAboveCell000032112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112013) h))

theorem cover_subtree_0a1ef543bda5 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112020
        (by
          have h : ((childLL thetaAboveCell000032112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112020) h)
        (by
          have h : ((childLH thetaAboveCell000032112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112020) h)
        (by
          have h : ((childHL thetaAboveCell000032112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112020) h)
        (by
          have h : ((childHH thetaAboveCell000032112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112021
        (by
          have h : ((childLL thetaAboveCell000032112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112021) h)
        (by
          have h : ((childLH thetaAboveCell000032112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112021) h)
        (by
          have h : ((childHL thetaAboveCell000032112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112021) h)
        (by
          have h : ((childHH thetaAboveCell000032112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112021) h))
    (by
      have h : (thetaAboveCell000032112022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112022 h)
    (by
      have h : (thetaAboveCell000032112023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112023 h)

theorem cover_subtree_26949ddfa0ff :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112030
        (by
          have h : ((childLL thetaAboveCell000032112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112030) h)
        (by
          have h : ((childLH thetaAboveCell000032112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112030) h)
        (by
          have h : ((childHL thetaAboveCell000032112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112030) h)
        (by
          have h : ((childHH thetaAboveCell000032112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112031
        (by
          have h : ((childLL thetaAboveCell000032112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112031) h)
        (by
          have h : ((childLH thetaAboveCell000032112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112031) h)
        (by
          have h : ((childHL thetaAboveCell000032112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112031) h)
        (by
          have h : ((childHH thetaAboveCell000032112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112031) h))
    (by
      have h : (thetaAboveCell000032112032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112032 h)
    (by
      have h : (thetaAboveCell000032112033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112033 h)

theorem e24KC2ThetaAboveLeaf0000321120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003211))
    cover_subtree_5921e16da435
    cover_subtree_52f1b09bd9bd
    cover_subtree_0a1ef543bda5
    cover_subtree_26949ddfa0ff
theorem cover_subtree_b04014698fa2 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032112100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112100 h)
    (by
      have h : (thetaAboveCell000032112101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112102
        (by
          have h : ((childLL thetaAboveCell000032112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112102) h)
        (by
          have h : ((childLH thetaAboveCell000032112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112102) h)
        (by
          have h : ((childHL thetaAboveCell000032112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112102) h)
        (by
          have h : ((childHH thetaAboveCell000032112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112103
        (by
          have h : ((childLL thetaAboveCell000032112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112103) h)
        (by
          have h : ((childLH thetaAboveCell000032112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112103) h)
        (by
          have h : ((childHL thetaAboveCell000032112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112103) h)
        (by
          have h : ((childHH thetaAboveCell000032112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112103) h))

theorem cover_subtree_49d16aafe784 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032112110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112110 h)
    (by
      have h : (thetaAboveCell000032112111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112112
        (by
          have h : ((childLL thetaAboveCell000032112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112112) h)
        (by
          have h : ((childLH thetaAboveCell000032112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112112) h)
        (by
          have h : ((childHL thetaAboveCell000032112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112112) h)
        (by
          have h : ((childHH thetaAboveCell000032112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112113
        (by
          have h : ((childLL thetaAboveCell000032112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112113) h)
        (by
          have h : ((childLH thetaAboveCell000032112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112113) h)
        (by
          have h : ((childHL thetaAboveCell000032112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112113) h)
        (by
          have h : ((childHH thetaAboveCell000032112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112113) h))

theorem cover_subtree_b7dcbd8da2a4 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112120
        (by
          have h : ((childLL thetaAboveCell000032112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112120) h)
        (by
          have h : ((childLH thetaAboveCell000032112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112120) h)
        (by
          have h : ((childHL thetaAboveCell000032112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112120) h)
        (by
          have h : ((childHH thetaAboveCell000032112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112121
        (by
          have h : ((childLL thetaAboveCell000032112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112121) h)
        (by
          have h : ((childLH thetaAboveCell000032112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112121) h)
        (by
          have h : ((childHL thetaAboveCell000032112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112121) h)
        (by
          have h : ((childHH thetaAboveCell000032112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112121) h))
    (by
      have h : (thetaAboveCell000032112122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112122 h)
    (by
      have h : (thetaAboveCell000032112123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112123 h)

theorem cover_subtree_fb1811cd44df :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112130
        (by
          have h : ((childLL thetaAboveCell000032112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112130) h)
        (by
          have h : ((childLH thetaAboveCell000032112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112130) h)
        (by
          have h : ((childHL thetaAboveCell000032112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112130) h)
        (by
          have h : ((childHH thetaAboveCell000032112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032112131
        (by
          have h : ((childLL thetaAboveCell000032112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032112131) h)
        (by
          have h : ((childLH thetaAboveCell000032112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032112131) h)
        (by
          have h : ((childHL thetaAboveCell000032112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032112131) h)
        (by
          have h : ((childHH thetaAboveCell000032112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032112131) h))
    (by
      have h : (thetaAboveCell000032112132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112132 h)
    (by
      have h : (thetaAboveCell000032112133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032112133 h)

theorem e24KC2ThetaAboveLeaf0000321121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003211))
    cover_subtree_b04014698fa2
    cover_subtree_49d16aafe784
    cover_subtree_b7dcbd8da2a4
    cover_subtree_fb1811cd44df
theorem e24KC2ThetaAboveLeaf0000321122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003211))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003211))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003211))) h)
theorem cover_subtree_6f17b9dcfe31 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032113000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113000 h)
    (by
      have h : (thetaAboveCell000032113001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113002
        (by
          have h : ((childLL thetaAboveCell000032113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113002) h)
        (by
          have h : ((childLH thetaAboveCell000032113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113002) h)
        (by
          have h : ((childHL thetaAboveCell000032113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113002) h)
        (by
          have h : ((childHH thetaAboveCell000032113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113003
        (by
          have h : ((childLL thetaAboveCell000032113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113003) h)
        (by
          have h : ((childLH thetaAboveCell000032113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113003) h)
        (by
          have h : ((childHL thetaAboveCell000032113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113003) h)
        (by
          have h : ((childHH thetaAboveCell000032113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113003) h))

theorem cover_subtree_bf78b444527b :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032113010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113010 h)
    (by
      have h : (thetaAboveCell000032113011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113012
        (by
          have h : ((childLL thetaAboveCell000032113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113012) h)
        (by
          have h : ((childLH thetaAboveCell000032113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113012) h)
        (by
          have h : ((childHL thetaAboveCell000032113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113012) h)
        (by
          have h : ((childHH thetaAboveCell000032113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113013
        (by
          have h : ((childLL thetaAboveCell000032113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113013) h)
        (by
          have h : ((childLH thetaAboveCell000032113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113013) h)
        (by
          have h : ((childHL thetaAboveCell000032113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113013) h)
        (by
          have h : ((childHH thetaAboveCell000032113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113013) h))

theorem cover_subtree_68fa0f6b74ff :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113020
        (by
          have h : ((childLL thetaAboveCell000032113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113020) h)
        (by
          have h : ((childLH thetaAboveCell000032113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113020) h)
        (by
          have h : ((childHL thetaAboveCell000032113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113020) h)
        (by
          have h : ((childHH thetaAboveCell000032113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113021
        (by
          have h : ((childLL thetaAboveCell000032113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113021) h)
        (by
          have h : ((childLH thetaAboveCell000032113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113021) h)
        (by
          have h : ((childHL thetaAboveCell000032113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113021) h)
        (by
          have h : ((childHH thetaAboveCell000032113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113021) h))
    (by
      have h : (thetaAboveCell000032113022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113022 h)
    (by
      have h : (thetaAboveCell000032113023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113023 h)

theorem cover_subtree_00b90c74e0b1 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113030
        (by
          have h : ((childLL thetaAboveCell000032113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113030) h)
        (by
          have h : ((childLH thetaAboveCell000032113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113030) h)
        (by
          have h : ((childHL thetaAboveCell000032113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113030) h)
        (by
          have h : ((childHH thetaAboveCell000032113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113031
        (by
          have h : ((childLL thetaAboveCell000032113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113031) h)
        (by
          have h : ((childLH thetaAboveCell000032113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113031) h)
        (by
          have h : ((childHL thetaAboveCell000032113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113031) h)
        (by
          have h : ((childHH thetaAboveCell000032113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113031) h))
    (by
      have h : (thetaAboveCell000032113032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113032 h)
    (by
      have h : (thetaAboveCell000032113033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113033 h)

theorem e24KC2ThetaAboveLeaf0000321130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003211))
    cover_subtree_6f17b9dcfe31
    cover_subtree_bf78b444527b
    cover_subtree_68fa0f6b74ff
    cover_subtree_00b90c74e0b1
theorem cover_subtree_bd2e141553af :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032113100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113100 h)
    (by
      have h : (thetaAboveCell000032113101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113102
        (by
          have h : ((childLL thetaAboveCell000032113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113102) h)
        (by
          have h : ((childLH thetaAboveCell000032113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113102) h)
        (by
          have h : ((childHL thetaAboveCell000032113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113102) h)
        (by
          have h : ((childHH thetaAboveCell000032113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113103
        (by
          have h : ((childLL thetaAboveCell000032113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113103) h)
        (by
          have h : ((childLH thetaAboveCell000032113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113103) h)
        (by
          have h : ((childHL thetaAboveCell000032113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113103) h)
        (by
          have h : ((childHH thetaAboveCell000032113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113103) h))

theorem cover_subtree_689bdaf91bf7 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003211)))
    (by
      have h : (thetaAboveCell000032113110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113110 h)
    (by
      have h : (thetaAboveCell000032113111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113112
        (by
          have h : ((childLL thetaAboveCell000032113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113112) h)
        (by
          have h : ((childLH thetaAboveCell000032113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113112) h)
        (by
          have h : ((childHL thetaAboveCell000032113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113112) h)
        (by
          have h : ((childHH thetaAboveCell000032113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113113
        (by
          have h : ((childLL thetaAboveCell000032113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113113) h)
        (by
          have h : ((childLH thetaAboveCell000032113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113113) h)
        (by
          have h : ((childHL thetaAboveCell000032113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113113) h)
        (by
          have h : ((childHH thetaAboveCell000032113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113113) h))

theorem cover_subtree_0feb1fef76ea :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113120
        (by
          have h : ((childLL thetaAboveCell000032113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113120) h)
        (by
          have h : ((childLH thetaAboveCell000032113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113120) h)
        (by
          have h : ((childHL thetaAboveCell000032113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113120) h)
        (by
          have h : ((childHH thetaAboveCell000032113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113121
        (by
          have h : ((childLL thetaAboveCell000032113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113121) h)
        (by
          have h : ((childLH thetaAboveCell000032113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113121) h)
        (by
          have h : ((childHL thetaAboveCell000032113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113121) h)
        (by
          have h : ((childHH thetaAboveCell000032113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113121) h))
    (by
      have h : (thetaAboveCell000032113122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113122 h)
    (by
      have h : (thetaAboveCell000032113123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113123 h)

theorem cover_subtree_5f404684ac08 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003211)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113130
        (by
          have h : ((childLL thetaAboveCell000032113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113130) h)
        (by
          have h : ((childLH thetaAboveCell000032113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113130) h)
        (by
          have h : ((childHL thetaAboveCell000032113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113130) h)
        (by
          have h : ((childHH thetaAboveCell000032113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113131
        (by
          have h : ((childLL thetaAboveCell000032113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113131) h)
        (by
          have h : ((childLH thetaAboveCell000032113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113131) h)
        (by
          have h : ((childHL thetaAboveCell000032113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113131) h)
        (by
          have h : ((childHH thetaAboveCell000032113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113131) h))
    (by
      have h : (thetaAboveCell000032113132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000032113132 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000032113133
        (by
          have h : ((childLL thetaAboveCell000032113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000032113133) h)
        (by
          have h : ((childLH thetaAboveCell000032113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000032113133) h)
        (by
          have h : ((childHL thetaAboveCell000032113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000032113133) h)
        (by
          have h : ((childHH thetaAboveCell000032113133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000032113133) h))

theorem e24KC2ThetaAboveLeaf0000321131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003211))
    cover_subtree_bd2e141553af
    cover_subtree_689bdaf91bf7
    cover_subtree_0feb1fef76ea
    cover_subtree_5f404684ac08
theorem e24KC2ThetaAboveLeaf0000321132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003211))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000321133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003211))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003211))) h)
theorem e24KC2ThetaAboveLeaf0000330002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003300))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003300))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003300))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003300))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003300))) h)
theorem cover_subtree_307fcc32307f :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033002000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002000 h)
    (by
      have h : (thetaAboveCell000033002001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002002
        (by
          have h : ((childLL thetaAboveCell000033002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002002) h)
        (by
          have h : ((childLH thetaAboveCell000033002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002002) h)
        (by
          have h : ((childHL thetaAboveCell000033002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002002) h)
        (by
          have h : ((childHH thetaAboveCell000033002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002003
        (by
          have h : ((childLL thetaAboveCell000033002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002003) h)
        (by
          have h : ((childLH thetaAboveCell000033002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002003) h)
        (by
          have h : ((childHL thetaAboveCell000033002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002003) h)
        (by
          have h : ((childHH thetaAboveCell000033002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002003) h))

theorem cover_subtree_d72d916d3b48 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033002010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002010 h)
    (by
      have h : (thetaAboveCell000033002011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002012
        (by
          have h : ((childLL thetaAboveCell000033002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002012) h)
        (by
          have h : ((childLH thetaAboveCell000033002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002012) h)
        (by
          have h : ((childHL thetaAboveCell000033002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002012) h)
        (by
          have h : ((childHH thetaAboveCell000033002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002013
        (by
          have h : ((childLL thetaAboveCell000033002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002013) h)
        (by
          have h : ((childLH thetaAboveCell000033002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002013) h)
        (by
          have h : ((childHL thetaAboveCell000033002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002013) h)
        (by
          have h : ((childHH thetaAboveCell000033002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002013) h))

theorem cover_subtree_68d4094c9ee3 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002020
        (by
          have h : ((childLL thetaAboveCell000033002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002020) h)
        (by
          have h : ((childLH thetaAboveCell000033002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002020) h)
        (by
          have h : ((childHL thetaAboveCell000033002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002020) h)
        (by
          have h : ((childHH thetaAboveCell000033002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002021
        (by
          have h : ((childLL thetaAboveCell000033002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002021) h)
        (by
          have h : ((childLH thetaAboveCell000033002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002021) h)
        (by
          have h : ((childHL thetaAboveCell000033002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002021) h)
        (by
          have h : ((childHH thetaAboveCell000033002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002022
        (by
          have h : ((childLL thetaAboveCell000033002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002022) h)
        (by
          have h : ((childLH thetaAboveCell000033002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002022) h)
        (by
          have h : ((childHL thetaAboveCell000033002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002022) h)
        (by
          have h : ((childHH thetaAboveCell000033002022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002023
        (by
          have h : ((childLL thetaAboveCell000033002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002023) h)
        (by
          have h : ((childLH thetaAboveCell000033002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002023) h)
        (by
          have h : ((childHL thetaAboveCell000033002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002023) h)
        (by
          have h : ((childHH thetaAboveCell000033002023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002023) h))

theorem cover_subtree_133a2eba8f2a :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002030
        (by
          have h : ((childLL thetaAboveCell000033002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002030) h)
        (by
          have h : ((childLH thetaAboveCell000033002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002030) h)
        (by
          have h : ((childHL thetaAboveCell000033002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002030) h)
        (by
          have h : ((childHH thetaAboveCell000033002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002031
        (by
          have h : ((childLL thetaAboveCell000033002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002031) h)
        (by
          have h : ((childLH thetaAboveCell000033002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002031) h)
        (by
          have h : ((childHL thetaAboveCell000033002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002031) h)
        (by
          have h : ((childHH thetaAboveCell000033002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002032
        (by
          have h : ((childLL thetaAboveCell000033002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002032) h)
        (by
          have h : ((childLH thetaAboveCell000033002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002032) h)
        (by
          have h : ((childHL thetaAboveCell000033002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002032) h)
        (by
          have h : ((childHH thetaAboveCell000033002032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002033
        (by
          have h : ((childLL thetaAboveCell000033002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002033) h)
        (by
          have h : ((childLH thetaAboveCell000033002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002033) h)
        (by
          have h : ((childHL thetaAboveCell000033002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002033) h)
        (by
          have h : ((childHH thetaAboveCell000033002033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002033) h))

theorem e24KC2ThetaAboveLeaf0000330020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003300))
    cover_subtree_307fcc32307f
    cover_subtree_d72d916d3b48
    cover_subtree_68d4094c9ee3
    cover_subtree_133a2eba8f2a
theorem cover_subtree_81e0e7f5c28b :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033002100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002100 h)
    (by
      have h : (thetaAboveCell000033002101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002102
        (by
          have h : ((childLL thetaAboveCell000033002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002102) h)
        (by
          have h : ((childLH thetaAboveCell000033002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002102) h)
        (by
          have h : ((childHL thetaAboveCell000033002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002102) h)
        (by
          have h : ((childHH thetaAboveCell000033002102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002103
        (by
          have h : ((childLL thetaAboveCell000033002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002103) h)
        (by
          have h : ((childLH thetaAboveCell000033002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002103) h)
        (by
          have h : ((childHL thetaAboveCell000033002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002103) h)
        (by
          have h : ((childHH thetaAboveCell000033002103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002103) h))

theorem cover_subtree_db4d96344863 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033002110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002110 h)
    (by
      have h : (thetaAboveCell000033002111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033002111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002112
        (by
          have h : ((childLL thetaAboveCell000033002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002112) h)
        (by
          have h : ((childLH thetaAboveCell000033002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002112) h)
        (by
          have h : ((childHL thetaAboveCell000033002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002112) h)
        (by
          have h : ((childHH thetaAboveCell000033002112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002113
        (by
          have h : ((childLL thetaAboveCell000033002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002113) h)
        (by
          have h : ((childLH thetaAboveCell000033002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002113) h)
        (by
          have h : ((childHL thetaAboveCell000033002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002113) h)
        (by
          have h : ((childHH thetaAboveCell000033002113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002113) h))

theorem cover_subtree_f83decf107d3 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002120
        (by
          have h : ((childLL thetaAboveCell000033002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002120) h)
        (by
          have h : ((childLH thetaAboveCell000033002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002120) h)
        (by
          have h : ((childHL thetaAboveCell000033002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002120) h)
        (by
          have h : ((childHH thetaAboveCell000033002120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002121
        (by
          have h : ((childLL thetaAboveCell000033002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002121) h)
        (by
          have h : ((childLH thetaAboveCell000033002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002121) h)
        (by
          have h : ((childHL thetaAboveCell000033002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002121) h)
        (by
          have h : ((childHH thetaAboveCell000033002121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002122
        (by
          have h : ((childLL thetaAboveCell000033002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002122) h)
        (by
          have h : ((childLH thetaAboveCell000033002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002122) h)
        (by
          have h : ((childHL thetaAboveCell000033002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002122) h)
        (by
          have h : ((childHH thetaAboveCell000033002122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002123
        (by
          have h : ((childLL thetaAboveCell000033002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002123) h)
        (by
          have h : ((childLH thetaAboveCell000033002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002123) h)
        (by
          have h : ((childHL thetaAboveCell000033002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002123) h)
        (by
          have h : ((childHH thetaAboveCell000033002123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002123) h))

theorem cover_subtree_aa2cd6339b25 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002130
        (by
          have h : ((childLL thetaAboveCell000033002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002130) h)
        (by
          have h : ((childLH thetaAboveCell000033002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002130) h)
        (by
          have h : ((childHL thetaAboveCell000033002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002130) h)
        (by
          have h : ((childHH thetaAboveCell000033002130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002131
        (by
          have h : ((childLL thetaAboveCell000033002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002131) h)
        (by
          have h : ((childLH thetaAboveCell000033002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002131) h)
        (by
          have h : ((childHL thetaAboveCell000033002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002131) h)
        (by
          have h : ((childHH thetaAboveCell000033002131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002132
        (by
          have h : ((childLL thetaAboveCell000033002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002132) h)
        (by
          have h : ((childLH thetaAboveCell000033002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002132) h)
        (by
          have h : ((childHL thetaAboveCell000033002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002132) h)
        (by
          have h : ((childHH thetaAboveCell000033002132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033002133
        (by
          have h : ((childLL thetaAboveCell000033002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033002133) h)
        (by
          have h : ((childLH thetaAboveCell000033002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033002133) h)
        (by
          have h : ((childHL thetaAboveCell000033002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033002133) h)
        (by
          have h : ((childHH thetaAboveCell000033002133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033002133) h))

theorem e24KC2ThetaAboveLeaf0000330021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003300))
    cover_subtree_81e0e7f5c28b
    cover_subtree_db4d96344863
    cover_subtree_f83decf107d3
    cover_subtree_aa2cd6339b25
theorem e24KC2ThetaAboveLeaf0000330022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003300))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003300))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003300))) h)
theorem cover_subtree_9d0a80f57bd8 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033003000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003000 h)
    (by
      have h : (thetaAboveCell000033003001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003002
        (by
          have h : ((childLL thetaAboveCell000033003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003002) h)
        (by
          have h : ((childLH thetaAboveCell000033003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003002) h)
        (by
          have h : ((childHL thetaAboveCell000033003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003002) h)
        (by
          have h : ((childHH thetaAboveCell000033003002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003003
        (by
          have h : ((childLL thetaAboveCell000033003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003003) h)
        (by
          have h : ((childLH thetaAboveCell000033003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003003) h)
        (by
          have h : ((childHL thetaAboveCell000033003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003003) h)
        (by
          have h : ((childHH thetaAboveCell000033003003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003003) h))

theorem cover_subtree_dc4f306f6518 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033003010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003010 h)
    (by
      have h : (thetaAboveCell000033003011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003012
        (by
          have h : ((childLL thetaAboveCell000033003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003012) h)
        (by
          have h : ((childLH thetaAboveCell000033003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003012) h)
        (by
          have h : ((childHL thetaAboveCell000033003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003012) h)
        (by
          have h : ((childHH thetaAboveCell000033003012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003013
        (by
          have h : ((childLL thetaAboveCell000033003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003013) h)
        (by
          have h : ((childLH thetaAboveCell000033003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003013) h)
        (by
          have h : ((childHL thetaAboveCell000033003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003013) h)
        (by
          have h : ((childHH thetaAboveCell000033003013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003013) h))

theorem cover_subtree_f02da567f8d1 :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003020
        (by
          have h : ((childLL thetaAboveCell000033003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003020) h)
        (by
          have h : ((childLH thetaAboveCell000033003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003020) h)
        (by
          have h : ((childHL thetaAboveCell000033003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003020) h)
        (by
          have h : ((childHH thetaAboveCell000033003020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003021
        (by
          have h : ((childLL thetaAboveCell000033003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003021) h)
        (by
          have h : ((childLH thetaAboveCell000033003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003021) h)
        (by
          have h : ((childHL thetaAboveCell000033003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003021) h)
        (by
          have h : ((childHH thetaAboveCell000033003021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003022
        (by
          have h : ((childLL thetaAboveCell000033003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003022) h)
        (by
          have h : ((childLH thetaAboveCell000033003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003022) h)
        (by
          have h : ((childHL thetaAboveCell000033003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003022) h)
        (by
          have h : ((childHH thetaAboveCell000033003022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003023
        (by
          have h : ((childLL thetaAboveCell000033003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003023) h)
        (by
          have h : ((childLH thetaAboveCell000033003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003023) h)
        (by
          have h : ((childHL thetaAboveCell000033003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003023) h)
        (by
          have h : ((childHH thetaAboveCell000033003023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003023) h))

theorem cover_subtree_5b244ca5864c :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003030
        (by
          have h : ((childLL thetaAboveCell000033003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003030) h)
        (by
          have h : ((childLH thetaAboveCell000033003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003030) h)
        (by
          have h : ((childHL thetaAboveCell000033003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003030) h)
        (by
          have h : ((childHH thetaAboveCell000033003030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003031
        (by
          have h : ((childLL thetaAboveCell000033003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003031) h)
        (by
          have h : ((childLH thetaAboveCell000033003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003031) h)
        (by
          have h : ((childHL thetaAboveCell000033003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003031) h)
        (by
          have h : ((childHH thetaAboveCell000033003031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003032
        (by
          have h : ((childLL thetaAboveCell000033003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003032) h)
        (by
          have h : ((childLH thetaAboveCell000033003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003032) h)
        (by
          have h : ((childHL thetaAboveCell000033003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003032) h)
        (by
          have h : ((childHH thetaAboveCell000033003032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003033
        (by
          have h : ((childLL thetaAboveCell000033003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003033) h)
        (by
          have h : ((childLH thetaAboveCell000033003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003033) h)
        (by
          have h : ((childHL thetaAboveCell000033003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003033) h)
        (by
          have h : ((childHH thetaAboveCell000033003033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003033) h))

theorem e24KC2ThetaAboveLeaf0000330030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003300))
    cover_subtree_9d0a80f57bd8
    cover_subtree_dc4f306f6518
    cover_subtree_f02da567f8d1
    cover_subtree_5b244ca5864c
theorem cover_subtree_834d2353fe6e :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033003100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003100 h)
    (by
      have h : (thetaAboveCell000033003101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003102
        (by
          have h : ((childLL thetaAboveCell000033003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003102) h)
        (by
          have h : ((childLH thetaAboveCell000033003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003102) h)
        (by
          have h : ((childHL thetaAboveCell000033003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003102) h)
        (by
          have h : ((childHH thetaAboveCell000033003102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003103
        (by
          have h : ((childLL thetaAboveCell000033003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003103) h)
        (by
          have h : ((childLH thetaAboveCell000033003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003103) h)
        (by
          have h : ((childHL thetaAboveCell000033003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003103) h)
        (by
          have h : ((childHH thetaAboveCell000033003103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003103) h))

theorem cover_subtree_d145e983fe8d :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003300)))
    (by
      have h : (thetaAboveCell000033003110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003110 h)
    (by
      have h : (thetaAboveCell000033003111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033003111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003112
        (by
          have h : ((childLL thetaAboveCell000033003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003112) h)
        (by
          have h : ((childLH thetaAboveCell000033003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003112) h)
        (by
          have h : ((childHL thetaAboveCell000033003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003112) h)
        (by
          have h : ((childHH thetaAboveCell000033003112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003113
        (by
          have h : ((childLL thetaAboveCell000033003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003113) h)
        (by
          have h : ((childLH thetaAboveCell000033003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003113) h)
        (by
          have h : ((childHL thetaAboveCell000033003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003113) h)
        (by
          have h : ((childHH thetaAboveCell000033003113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003113) h))

theorem cover_subtree_d12e61a2b3bb :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003120
        (by
          have h : ((childLL thetaAboveCell000033003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003120) h)
        (by
          have h : ((childLH thetaAboveCell000033003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003120) h)
        (by
          have h : ((childHL thetaAboveCell000033003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003120) h)
        (by
          have h : ((childHH thetaAboveCell000033003120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003121
        (by
          have h : ((childLL thetaAboveCell000033003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003121) h)
        (by
          have h : ((childLH thetaAboveCell000033003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003121) h)
        (by
          have h : ((childHL thetaAboveCell000033003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003121) h)
        (by
          have h : ((childHH thetaAboveCell000033003121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003122
        (by
          have h : ((childLL thetaAboveCell000033003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003122) h)
        (by
          have h : ((childLH thetaAboveCell000033003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003122) h)
        (by
          have h : ((childHL thetaAboveCell000033003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003122) h)
        (by
          have h : ((childHH thetaAboveCell000033003122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003123
        (by
          have h : ((childLL thetaAboveCell000033003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003123) h)
        (by
          have h : ((childLH thetaAboveCell000033003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003123) h)
        (by
          have h : ((childHL thetaAboveCell000033003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003123) h)
        (by
          have h : ((childHH thetaAboveCell000033003123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003123) h))

theorem cover_subtree_19725b594124 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003300))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003300)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003130
        (by
          have h : ((childLL thetaAboveCell000033003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003130) h)
        (by
          have h : ((childLH thetaAboveCell000033003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003130) h)
        (by
          have h : ((childHL thetaAboveCell000033003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003130) h)
        (by
          have h : ((childHH thetaAboveCell000033003130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003131
        (by
          have h : ((childLL thetaAboveCell000033003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003131) h)
        (by
          have h : ((childLH thetaAboveCell000033003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003131) h)
        (by
          have h : ((childHL thetaAboveCell000033003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003131) h)
        (by
          have h : ((childHH thetaAboveCell000033003131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003132
        (by
          have h : ((childLL thetaAboveCell000033003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003132) h)
        (by
          have h : ((childLH thetaAboveCell000033003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003132) h)
        (by
          have h : ((childHL thetaAboveCell000033003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003132) h)
        (by
          have h : ((childHH thetaAboveCell000033003132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033003133
        (by
          have h : ((childLL thetaAboveCell000033003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033003133) h)
        (by
          have h : ((childLH thetaAboveCell000033003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033003133) h)
        (by
          have h : ((childHL thetaAboveCell000033003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033003133) h)
        (by
          have h : ((childHH thetaAboveCell000033003133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033003133) h))

theorem e24KC2ThetaAboveLeaf0000330031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003300))
    cover_subtree_834d2353fe6e
    cover_subtree_d145e983fe8d
    cover_subtree_d12e61a2b3bb
    cover_subtree_19725b594124
theorem e24KC2ThetaAboveLeaf0000330032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003300))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003300))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003300))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003300))) h)
theorem e24KC2ThetaAboveLeaf0000330102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003301))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003301))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003301))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003301))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003301))) h)
theorem cover_subtree_8335c3bf0b1b :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033012000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012000 h)
    (by
      have h : (thetaAboveCell000033012001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012002
        (by
          have h : ((childLL thetaAboveCell000033012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012002) h)
        (by
          have h : ((childLH thetaAboveCell000033012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012002) h)
        (by
          have h : ((childHL thetaAboveCell000033012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012002) h)
        (by
          have h : ((childHH thetaAboveCell000033012002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012003
        (by
          have h : ((childLL thetaAboveCell000033012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012003) h)
        (by
          have h : ((childLH thetaAboveCell000033012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012003) h)
        (by
          have h : ((childHL thetaAboveCell000033012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012003) h)
        (by
          have h : ((childHH thetaAboveCell000033012003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012003) h))

theorem cover_subtree_020729332332 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033012010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012010 h)
    (by
      have h : (thetaAboveCell000033012011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012012
        (by
          have h : ((childLL thetaAboveCell000033012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012012) h)
        (by
          have h : ((childLH thetaAboveCell000033012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012012) h)
        (by
          have h : ((childHL thetaAboveCell000033012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012012) h)
        (by
          have h : ((childHH thetaAboveCell000033012012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012013
        (by
          have h : ((childLL thetaAboveCell000033012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012013) h)
        (by
          have h : ((childLH thetaAboveCell000033012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012013) h)
        (by
          have h : ((childHL thetaAboveCell000033012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012013) h)
        (by
          have h : ((childHH thetaAboveCell000033012013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012013) h))

theorem cover_subtree_f21e4f8d9787 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012020
        (by
          have h : ((childLL thetaAboveCell000033012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012020) h)
        (by
          have h : ((childLH thetaAboveCell000033012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012020) h)
        (by
          have h : ((childHL thetaAboveCell000033012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012020) h)
        (by
          have h : ((childHH thetaAboveCell000033012020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012021
        (by
          have h : ((childLL thetaAboveCell000033012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012021) h)
        (by
          have h : ((childLH thetaAboveCell000033012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012021) h)
        (by
          have h : ((childHL thetaAboveCell000033012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012021) h)
        (by
          have h : ((childHH thetaAboveCell000033012021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012022
        (by
          have h : ((childLL thetaAboveCell000033012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012022) h)
        (by
          have h : ((childLH thetaAboveCell000033012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012022) h)
        (by
          have h : ((childHL thetaAboveCell000033012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012022) h)
        (by
          have h : ((childHH thetaAboveCell000033012022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012023
        (by
          have h : ((childLL thetaAboveCell000033012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012023) h)
        (by
          have h : ((childLH thetaAboveCell000033012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012023) h)
        (by
          have h : ((childHL thetaAboveCell000033012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012023) h)
        (by
          have h : ((childHH thetaAboveCell000033012023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012023) h))

theorem cover_subtree_bb534365ac4e :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012030
        (by
          have h : ((childLL thetaAboveCell000033012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012030) h)
        (by
          have h : ((childLH thetaAboveCell000033012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012030) h)
        (by
          have h : ((childHL thetaAboveCell000033012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012030) h)
        (by
          have h : ((childHH thetaAboveCell000033012030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012031
        (by
          have h : ((childLL thetaAboveCell000033012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012031) h)
        (by
          have h : ((childLH thetaAboveCell000033012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012031) h)
        (by
          have h : ((childHL thetaAboveCell000033012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012031) h)
        (by
          have h : ((childHH thetaAboveCell000033012031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012032
        (by
          have h : ((childLL thetaAboveCell000033012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012032) h)
        (by
          have h : ((childLH thetaAboveCell000033012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012032) h)
        (by
          have h : ((childHL thetaAboveCell000033012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012032) h)
        (by
          have h : ((childHH thetaAboveCell000033012032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012033
        (by
          have h : ((childLL thetaAboveCell000033012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012033) h)
        (by
          have h : ((childLH thetaAboveCell000033012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012033) h)
        (by
          have h : ((childHL thetaAboveCell000033012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012033) h)
        (by
          have h : ((childHH thetaAboveCell000033012033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012033) h))

theorem e24KC2ThetaAboveLeaf0000330120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003301))
    cover_subtree_8335c3bf0b1b
    cover_subtree_020729332332
    cover_subtree_f21e4f8d9787
    cover_subtree_bb534365ac4e
theorem cover_subtree_2bf93d8ac027 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033012100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012100 h)
    (by
      have h : (thetaAboveCell000033012101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012102
        (by
          have h : ((childLL thetaAboveCell000033012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012102) h)
        (by
          have h : ((childLH thetaAboveCell000033012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012102) h)
        (by
          have h : ((childHL thetaAboveCell000033012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012102) h)
        (by
          have h : ((childHH thetaAboveCell000033012102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012103
        (by
          have h : ((childLL thetaAboveCell000033012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012103) h)
        (by
          have h : ((childLH thetaAboveCell000033012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012103) h)
        (by
          have h : ((childHL thetaAboveCell000033012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012103) h)
        (by
          have h : ((childHH thetaAboveCell000033012103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012103) h))

theorem cover_subtree_1f4c8299dae5 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033012110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012110 h)
    (by
      have h : (thetaAboveCell000033012111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012112
        (by
          have h : ((childLL thetaAboveCell000033012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012112) h)
        (by
          have h : ((childLH thetaAboveCell000033012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012112) h)
        (by
          have h : ((childHL thetaAboveCell000033012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012112) h)
        (by
          have h : ((childHH thetaAboveCell000033012112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012113
        (by
          have h : ((childLL thetaAboveCell000033012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012113) h)
        (by
          have h : ((childLH thetaAboveCell000033012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012113) h)
        (by
          have h : ((childHL thetaAboveCell000033012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012113) h)
        (by
          have h : ((childHH thetaAboveCell000033012113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012113) h))

theorem cover_subtree_6e263eab4641 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012120
        (by
          have h : ((childLL thetaAboveCell000033012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012120) h)
        (by
          have h : ((childLH thetaAboveCell000033012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012120) h)
        (by
          have h : ((childHL thetaAboveCell000033012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012120) h)
        (by
          have h : ((childHH thetaAboveCell000033012120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012121
        (by
          have h : ((childLL thetaAboveCell000033012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012121) h)
        (by
          have h : ((childLH thetaAboveCell000033012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012121) h)
        (by
          have h : ((childHL thetaAboveCell000033012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012121) h)
        (by
          have h : ((childHH thetaAboveCell000033012121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012122
        (by
          have h : ((childLL thetaAboveCell000033012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012122) h)
        (by
          have h : ((childLH thetaAboveCell000033012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012122) h)
        (by
          have h : ((childHL thetaAboveCell000033012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012122) h)
        (by
          have h : ((childHH thetaAboveCell000033012122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012123
        (by
          have h : ((childLL thetaAboveCell000033012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012123) h)
        (by
          have h : ((childLH thetaAboveCell000033012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012123) h)
        (by
          have h : ((childHL thetaAboveCell000033012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012123) h)
        (by
          have h : ((childHH thetaAboveCell000033012123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012123) h))

theorem cover_subtree_d9fe12f58957 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012130
        (by
          have h : ((childLL thetaAboveCell000033012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012130) h)
        (by
          have h : ((childLH thetaAboveCell000033012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012130) h)
        (by
          have h : ((childHL thetaAboveCell000033012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012130) h)
        (by
          have h : ((childHH thetaAboveCell000033012130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012131
        (by
          have h : ((childLL thetaAboveCell000033012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012131) h)
        (by
          have h : ((childLH thetaAboveCell000033012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012131) h)
        (by
          have h : ((childHL thetaAboveCell000033012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012131) h)
        (by
          have h : ((childHH thetaAboveCell000033012131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012132
        (by
          have h : ((childLL thetaAboveCell000033012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012132) h)
        (by
          have h : ((childLH thetaAboveCell000033012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012132) h)
        (by
          have h : ((childHL thetaAboveCell000033012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012132) h)
        (by
          have h : ((childHH thetaAboveCell000033012132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033012133
        (by
          have h : ((childLL thetaAboveCell000033012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033012133) h)
        (by
          have h : ((childLH thetaAboveCell000033012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033012133) h)
        (by
          have h : ((childHL thetaAboveCell000033012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033012133) h)
        (by
          have h : ((childHH thetaAboveCell000033012133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033012133) h))

theorem e24KC2ThetaAboveLeaf0000330121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003301))
    cover_subtree_2bf93d8ac027
    cover_subtree_1f4c8299dae5
    cover_subtree_6e263eab4641
    cover_subtree_d9fe12f58957
theorem e24KC2ThetaAboveLeaf0000330122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012200 h)
        (by
          have h : (thetaAboveCell000033012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012201 h)
        (by
          have h : (thetaAboveCell000033012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012202 h)
        (by
          have h : (thetaAboveCell000033012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012210 h)
        (by
          have h : (thetaAboveCell000033012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012211 h)
        (by
          have h : (thetaAboveCell000033012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012212 h)
        (by
          have h : (thetaAboveCell000033012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012300 h)
        (by
          have h : (thetaAboveCell000033012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012301 h)
        (by
          have h : (thetaAboveCell000033012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012302 h)
        (by
          have h : (thetaAboveCell000033012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012310 h)
        (by
          have h : (thetaAboveCell000033012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012311 h)
        (by
          have h : (thetaAboveCell000033012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012312 h)
        (by
          have h : (thetaAboveCell000033012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003301))) h)
theorem cover_subtree_3ee7d70a5db3 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033013000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013000 h)
    (by
      have h : (thetaAboveCell000033013001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013002
        (by
          have h : ((childLL thetaAboveCell000033013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013002) h)
        (by
          have h : ((childLH thetaAboveCell000033013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013002) h)
        (by
          have h : ((childHL thetaAboveCell000033013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013002) h)
        (by
          have h : ((childHH thetaAboveCell000033013002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013003
        (by
          have h : ((childLL thetaAboveCell000033013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013003) h)
        (by
          have h : ((childLH thetaAboveCell000033013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013003) h)
        (by
          have h : ((childHL thetaAboveCell000033013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013003) h)
        (by
          have h : ((childHH thetaAboveCell000033013003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013003) h))

theorem cover_subtree_f6080530d2a9 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033013010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013010 h)
    (by
      have h : (thetaAboveCell000033013011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013012
        (by
          have h : ((childLL thetaAboveCell000033013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013012) h)
        (by
          have h : ((childLH thetaAboveCell000033013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013012) h)
        (by
          have h : ((childHL thetaAboveCell000033013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013012) h)
        (by
          have h : ((childHH thetaAboveCell000033013012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013013
        (by
          have h : ((childLL thetaAboveCell000033013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013013) h)
        (by
          have h : ((childLH thetaAboveCell000033013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013013) h)
        (by
          have h : ((childHL thetaAboveCell000033013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013013) h)
        (by
          have h : ((childHH thetaAboveCell000033013013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013013) h))

theorem cover_subtree_2e5606e732f5 :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013020
        (by
          have h : ((childLL thetaAboveCell000033013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013020) h)
        (by
          have h : ((childLH thetaAboveCell000033013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013020) h)
        (by
          have h : ((childHL thetaAboveCell000033013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013020) h)
        (by
          have h : ((childHH thetaAboveCell000033013020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013021
        (by
          have h : ((childLL thetaAboveCell000033013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013021) h)
        (by
          have h : ((childLH thetaAboveCell000033013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013021) h)
        (by
          have h : ((childHL thetaAboveCell000033013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013021) h)
        (by
          have h : ((childHH thetaAboveCell000033013021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013022
        (by
          have h : ((childLL thetaAboveCell000033013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013022) h)
        (by
          have h : ((childLH thetaAboveCell000033013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013022) h)
        (by
          have h : ((childHL thetaAboveCell000033013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013022) h)
        (by
          have h : ((childHH thetaAboveCell000033013022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013023
        (by
          have h : ((childLL thetaAboveCell000033013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013023) h)
        (by
          have h : ((childLH thetaAboveCell000033013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013023) h)
        (by
          have h : ((childHL thetaAboveCell000033013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013023) h)
        (by
          have h : ((childHH thetaAboveCell000033013023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013023) h))

theorem cover_subtree_6143158a1495 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013030
        (by
          have h : ((childLL thetaAboveCell000033013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013030) h)
        (by
          have h : ((childLH thetaAboveCell000033013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013030) h)
        (by
          have h : ((childHL thetaAboveCell000033013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013030) h)
        (by
          have h : ((childHH thetaAboveCell000033013030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013031
        (by
          have h : ((childLL thetaAboveCell000033013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013031) h)
        (by
          have h : ((childLH thetaAboveCell000033013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013031) h)
        (by
          have h : ((childHL thetaAboveCell000033013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013031) h)
        (by
          have h : ((childHH thetaAboveCell000033013031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013032
        (by
          have h : ((childLL thetaAboveCell000033013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013032) h)
        (by
          have h : ((childLH thetaAboveCell000033013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013032) h)
        (by
          have h : ((childHL thetaAboveCell000033013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013032) h)
        (by
          have h : ((childHH thetaAboveCell000033013032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013033
        (by
          have h : ((childLL thetaAboveCell000033013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013033) h)
        (by
          have h : ((childLH thetaAboveCell000033013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013033) h)
        (by
          have h : ((childHL thetaAboveCell000033013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013033) h)
        (by
          have h : ((childHH thetaAboveCell000033013033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013033) h))

theorem e24KC2ThetaAboveLeaf0000330130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003301))
    cover_subtree_3ee7d70a5db3
    cover_subtree_f6080530d2a9
    cover_subtree_2e5606e732f5
    cover_subtree_6143158a1495
theorem cover_subtree_fd7379f50292 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033013100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013100 h)
    (by
      have h : (thetaAboveCell000033013101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013102
        (by
          have h : ((childLL thetaAboveCell000033013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013102) h)
        (by
          have h : ((childLH thetaAboveCell000033013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013102) h)
        (by
          have h : ((childHL thetaAboveCell000033013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013102) h)
        (by
          have h : ((childHH thetaAboveCell000033013102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013103
        (by
          have h : ((childLL thetaAboveCell000033013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013103) h)
        (by
          have h : ((childLH thetaAboveCell000033013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013103) h)
        (by
          have h : ((childHL thetaAboveCell000033013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013103) h)
        (by
          have h : ((childHH thetaAboveCell000033013103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013103) h))

theorem cover_subtree_f974def6b3e0 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003301)))
    (by
      have h : (thetaAboveCell000033013110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013110 h)
    (by
      have h : (thetaAboveCell000033013111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013112
        (by
          have h : ((childLL thetaAboveCell000033013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013112) h)
        (by
          have h : ((childLH thetaAboveCell000033013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013112) h)
        (by
          have h : ((childHL thetaAboveCell000033013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013112) h)
        (by
          have h : ((childHH thetaAboveCell000033013112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013113
        (by
          have h : ((childLL thetaAboveCell000033013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013113) h)
        (by
          have h : ((childLH thetaAboveCell000033013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013113) h)
        (by
          have h : ((childHL thetaAboveCell000033013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013113) h)
        (by
          have h : ((childHH thetaAboveCell000033013113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013113) h))

theorem cover_subtree_d879dc743b47 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013120
        (by
          have h : ((childLL thetaAboveCell000033013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013120) h)
        (by
          have h : ((childLH thetaAboveCell000033013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013120) h)
        (by
          have h : ((childHL thetaAboveCell000033013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013120) h)
        (by
          have h : ((childHH thetaAboveCell000033013120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013121
        (by
          have h : ((childLL thetaAboveCell000033013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013121) h)
        (by
          have h : ((childLH thetaAboveCell000033013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013121) h)
        (by
          have h : ((childHL thetaAboveCell000033013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013121) h)
        (by
          have h : ((childHH thetaAboveCell000033013121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013122
        (by
          have h : ((childLL thetaAboveCell000033013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013122) h)
        (by
          have h : ((childLH thetaAboveCell000033013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013122) h)
        (by
          have h : ((childHL thetaAboveCell000033013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013122) h)
        (by
          have h : ((childHH thetaAboveCell000033013122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013123
        (by
          have h : ((childLL thetaAboveCell000033013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013123) h)
        (by
          have h : ((childLH thetaAboveCell000033013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013123) h)
        (by
          have h : ((childHL thetaAboveCell000033013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013123) h)
        (by
          have h : ((childHH thetaAboveCell000033013123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013123) h))

theorem cover_subtree_ebda71a3a487 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003301))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003301)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013130
        (by
          have h : ((childLL thetaAboveCell000033013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013130) h)
        (by
          have h : ((childLH thetaAboveCell000033013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013130) h)
        (by
          have h : ((childHL thetaAboveCell000033013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013130) h)
        (by
          have h : ((childHH thetaAboveCell000033013130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013131
        (by
          have h : ((childLL thetaAboveCell000033013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013131) h)
        (by
          have h : ((childLH thetaAboveCell000033013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013131) h)
        (by
          have h : ((childHL thetaAboveCell000033013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013131) h)
        (by
          have h : ((childHH thetaAboveCell000033013131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013132
        (by
          have h : ((childLL thetaAboveCell000033013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013132) h)
        (by
          have h : ((childLH thetaAboveCell000033013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013132) h)
        (by
          have h : ((childHL thetaAboveCell000033013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013132) h)
        (by
          have h : ((childHH thetaAboveCell000033013132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033013133
        (by
          have h : ((childLL thetaAboveCell000033013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033013133) h)
        (by
          have h : ((childLH thetaAboveCell000033013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033013133) h)
        (by
          have h : ((childHL thetaAboveCell000033013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033013133) h)
        (by
          have h : ((childHH thetaAboveCell000033013133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033013133) h))

theorem e24KC2ThetaAboveLeaf0000330131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003301))
    cover_subtree_fd7379f50292
    cover_subtree_f974def6b3e0
    cover_subtree_d879dc743b47
    cover_subtree_ebda71a3a487
theorem e24KC2ThetaAboveLeaf0000330132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013200 h)
        (by
          have h : (thetaAboveCell000033013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013201 h)
        (by
          have h : (thetaAboveCell000033013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013202 h)
        (by
          have h : (thetaAboveCell000033013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013210 h)
        (by
          have h : (thetaAboveCell000033013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013211 h)
        (by
          have h : (thetaAboveCell000033013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013212 h)
        (by
          have h : (thetaAboveCell000033013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000330133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013300 h)
        (by
          have h : (thetaAboveCell000033013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013301 h)
        (by
          have h : (thetaAboveCell000033013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013302 h)
        (by
          have h : (thetaAboveCell000033013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00003301)))
        (by
          have h : (thetaAboveCell000033013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013310 h)
        (by
          have h : (thetaAboveCell000033013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013311 h)
        (by
          have h : (thetaAboveCell000033013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013312 h)
        (by
          have h : (thetaAboveCell000033013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033013313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003301))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003301))) h)
theorem e24KC2ThetaAboveLeaf0000331002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003310))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003310))) h)
theorem e24KC2ThetaAboveLeaf0000331003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003310))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003310))) h)
theorem e24KC2ThetaAboveLeaf0000331012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003310))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003310))) h)
theorem e24KC2ThetaAboveLeaf0000331013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003310))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003310))) h)
theorem cover_subtree_01b17a5cfced :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033102000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102000 h)
    (by
      have h : (thetaAboveCell000033102001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102002
        (by
          have h : ((childLL thetaAboveCell000033102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102002) h)
        (by
          have h : ((childLH thetaAboveCell000033102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102002) h)
        (by
          have h : ((childHL thetaAboveCell000033102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102002) h)
        (by
          have h : ((childHH thetaAboveCell000033102002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102003
        (by
          have h : ((childLL thetaAboveCell000033102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102003) h)
        (by
          have h : ((childLH thetaAboveCell000033102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102003) h)
        (by
          have h : ((childHL thetaAboveCell000033102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102003) h)
        (by
          have h : ((childHH thetaAboveCell000033102003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102003) h))

theorem cover_subtree_26a3db88cf1e :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033102010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102010 h)
    (by
      have h : (thetaAboveCell000033102011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102012
        (by
          have h : ((childLL thetaAboveCell000033102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102012) h)
        (by
          have h : ((childLH thetaAboveCell000033102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102012) h)
        (by
          have h : ((childHL thetaAboveCell000033102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102012) h)
        (by
          have h : ((childHH thetaAboveCell000033102012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102013
        (by
          have h : ((childLL thetaAboveCell000033102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102013) h)
        (by
          have h : ((childLH thetaAboveCell000033102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102013) h)
        (by
          have h : ((childHL thetaAboveCell000033102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102013) h)
        (by
          have h : ((childHH thetaAboveCell000033102013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102013) h))

theorem cover_subtree_afbc4e7a5775 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102020
        (by
          have h : ((childLL thetaAboveCell000033102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102020) h)
        (by
          have h : ((childLH thetaAboveCell000033102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102020) h)
        (by
          have h : ((childHL thetaAboveCell000033102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102020) h)
        (by
          have h : ((childHH thetaAboveCell000033102020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102021
        (by
          have h : ((childLL thetaAboveCell000033102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102021) h)
        (by
          have h : ((childLH thetaAboveCell000033102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102021) h)
        (by
          have h : ((childHL thetaAboveCell000033102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102021) h)
        (by
          have h : ((childHH thetaAboveCell000033102021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102022
        (by
          have h : ((childLL thetaAboveCell000033102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102022) h)
        (by
          have h : ((childLH thetaAboveCell000033102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102022) h)
        (by
          have h : ((childHL thetaAboveCell000033102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102022) h)
        (by
          have h : ((childHH thetaAboveCell000033102022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102023
        (by
          have h : ((childLL thetaAboveCell000033102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102023) h)
        (by
          have h : ((childLH thetaAboveCell000033102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102023) h)
        (by
          have h : ((childHL thetaAboveCell000033102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102023) h)
        (by
          have h : ((childHH thetaAboveCell000033102023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102023) h))

theorem cover_subtree_0885b8dd2e23 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102030
        (by
          have h : ((childLL thetaAboveCell000033102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102030) h)
        (by
          have h : ((childLH thetaAboveCell000033102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102030) h)
        (by
          have h : ((childHL thetaAboveCell000033102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102030) h)
        (by
          have h : ((childHH thetaAboveCell000033102030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102031
        (by
          have h : ((childLL thetaAboveCell000033102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102031) h)
        (by
          have h : ((childLH thetaAboveCell000033102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102031) h)
        (by
          have h : ((childHL thetaAboveCell000033102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102031) h)
        (by
          have h : ((childHH thetaAboveCell000033102031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102032
        (by
          have h : ((childLL thetaAboveCell000033102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102032) h)
        (by
          have h : ((childLH thetaAboveCell000033102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102032) h)
        (by
          have h : ((childHL thetaAboveCell000033102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102032) h)
        (by
          have h : ((childHH thetaAboveCell000033102032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102033
        (by
          have h : ((childLL thetaAboveCell000033102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102033) h)
        (by
          have h : ((childLH thetaAboveCell000033102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102033) h)
        (by
          have h : ((childHL thetaAboveCell000033102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102033) h)
        (by
          have h : ((childHH thetaAboveCell000033102033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102033) h))

theorem e24KC2ThetaAboveLeaf0000331020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003310))
    cover_subtree_01b17a5cfced
    cover_subtree_26a3db88cf1e
    cover_subtree_afbc4e7a5775
    cover_subtree_0885b8dd2e23

end PartE
end GerverSofa

end

end

end

end

end

end
