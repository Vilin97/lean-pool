/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch015`.
* `GerverSofa.KernelOnly.PartE.Certificates.Batch019`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells2f4f8ea4fc

/-- Subcell `1111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1112 : AngleCell :=
  childHL (childLH (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1113 : AngleCell :=
  childHH (childLH (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1120 : AngleCell :=
  childLL (childHL (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1121 : AngleCell :=
  childLH (childHL (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1122 : AngleCell :=
  childHL (childHL (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1123 : AngleCell :=
  childHH (childHL (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1130 : AngleCell :=
  childLL (childHH (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1131 : AngleCell :=
  childLH (childHH (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1132 : AngleCell :=
  childHL (childHH (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `1133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell1133 : AngleCell :=
  childHH (childHH (childLH (childLH e24ThetaAboveRoot)))

/-- Subcell `0000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0001 : AngleCell :=
  childLH (childLL (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0002 : AngleCell :=
  childHL (childLL (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0003 : AngleCell :=
  childHH (childLL (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0012 : AngleCell :=
  childHL (childLH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0013 : AngleCell :=
  childHH (childLH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0030 : AngleCell :=
  childLL (childHH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0031 : AngleCell :=
  childLH (childHH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0032 : AngleCell :=
  childHL (childHH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0033 : AngleCell :=
  childHH (childHH (childLL (childLL e24ThetaBelowRoot)))

/-- Subcell `0100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0101 : AngleCell :=
  childLH (childLL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0102 : AngleCell :=
  childHL (childLL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0103 : AngleCell :=
  childHH (childLL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0112 : AngleCell :=
  childHL (childLH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0113 : AngleCell :=
  childHH (childLH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0120 : AngleCell :=
  childLL (childHL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0121 : AngleCell :=
  childLH (childHL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0122 : AngleCell :=
  childHL (childHL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0123 : AngleCell :=
  childHH (childHL (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0130 : AngleCell :=
  childLL (childHH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0131 : AngleCell :=
  childLH (childHH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0132 : AngleCell :=
  childHL (childHH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `0133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0133 : AngleCell :=
  childHH (childHH (childLH (childLL e24ThetaBelowRoot)))

/-- Subcell `1000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1001 : AngleCell :=
  childLH (childLL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1002 : AngleCell :=
  childHL (childLL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1003 : AngleCell :=
  childHH (childLL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1010 : AngleCell :=
  childLL (childLH (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1011 : AngleCell :=
  childLH (childLH (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1012 : AngleCell :=
  childHL (childLH (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1013 : AngleCell :=
  childHH (childLH (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1020 : AngleCell :=
  childLL (childHL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1021 : AngleCell :=
  childLH (childHL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `1022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1022 : AngleCell :=
  childHL (childHL (childLL (childLH e24ThetaBelowRoot)))

/-- Subcell `11112331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112331 : AngleCell :=
  childLH (childHH (childHH (childHL thetaAboveCell1111)))

/-- Subcell `11112332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112332 : AngleCell :=
  childHL (childHH (childHH (childHL thetaAboveCell1111)))

/-- Subcell `11112333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11112333 : AngleCell :=
  childHH (childHH (childHH (childHL thetaAboveCell1111)))

/-- Subcell `11113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113220 : AngleCell :=
  childLL (childHL (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113221 : AngleCell :=
  childLH (childHL (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113222 : AngleCell :=
  childHL (childHL (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113223 : AngleCell :=
  childHH (childHL (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113230 : AngleCell :=
  childLL (childHH (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113231 : AngleCell :=
  childLH (childHH (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113232 : AngleCell :=
  childHL (childHH (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113233 : AngleCell :=
  childHH (childHH (childHL (childHH thetaAboveCell1111)))

/-- Subcell `11113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113320 : AngleCell :=
  childLL (childHL (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113321 : AngleCell :=
  childLH (childHL (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113322 : AngleCell :=
  childHL (childHL (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113323 : AngleCell :=
  childHH (childHL (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113330 : AngleCell :=
  childLL (childHH (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113331 : AngleCell :=
  childLH (childHH (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113332 : AngleCell :=
  childHL (childHH (childHH (childHH thetaAboveCell1111)))

/-- Subcell `11113333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell11113333 : AngleCell :=
  childHH (childHH (childHH (childHH thetaAboveCell1111)))

/-- Subcell `10113030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1011)))

/-- Subcell `10113031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1011)))

/-- Subcell `10113032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1011)))

/-- Subcell `10113033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1011)))

/-- Subcell `10113110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1011)))

/-- Subcell `10113133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell10113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1011)))

end GerverSofa.PartE.CertificateCells2f4f8ea4fc

namespace GerverSofa.PartE.CertificateCells2d2385ed48

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0000)))

/-- Subcell `000022103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002210)))

/-- Subcell `000022110220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00002211)))

/-- Subcell `000022110221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00002211)))

/-- Subcell `000022110222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00002211)))

/-- Subcell `000022110223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00002211)))

/-- Subcell `000022110230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00002211)))

/-- Subcell `000022110231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00002211)))

/-- Subcell `000022110232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00002211)))

/-- Subcell `000022110233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00002211)))

/-- Subcell `000022110320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00002211)))

/-- Subcell `000022110321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00002211)))

/-- Subcell `000022110322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00002211)))

/-- Subcell `000022110323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00002211)))

/-- Subcell `000022110330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00002211)))

/-- Subcell `000022110331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00002211)))

/-- Subcell `000022110332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00002211)))

/-- Subcell `000022110333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022110333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00002211)))

/-- Subcell `000022111220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00002211)))

/-- Subcell `000022111221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00002211)))

/-- Subcell `000022111222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00002211)))

/-- Subcell `000022111223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00002211)))

/-- Subcell `000022111230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaAboveCell00002211)))

/-- Subcell `000022111231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaAboveCell00002211)))

/-- Subcell `000022111232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaAboveCell00002211)))

/-- Subcell `000022111233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaAboveCell00002211)))

/-- Subcell `000022111320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaAboveCell00002211)))

/-- Subcell `000022111321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaAboveCell00002211)))

/-- Subcell `000022111322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaAboveCell00002211)))

/-- Subcell `000022111323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaAboveCell00002211)))

/-- Subcell `000022111330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaAboveCell00002211)))

/-- Subcell `000022111331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaAboveCell00002211)))

/-- Subcell `000022111332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaAboveCell00002211)))

/-- Subcell `000022111333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022111333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaAboveCell00002211)))

/-- Subcell `000022112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00002211)))

/-- Subcell `000022112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00002211)))

/-- Subcell `000022113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00002211)))

/-- Subcell `000022113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000022113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002211)))

/-- Subcell `000023000220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00002300)))

/-- Subcell `000023000221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00002300)))

/-- Subcell `000023000222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00002300)))

/-- Subcell `000023000223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00002300)))

/-- Subcell `000023000230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00002300)))

/-- Subcell `000023000231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00002300)))

/-- Subcell `000023000232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00002300)))

/-- Subcell `000023000233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00002300)))

/-- Subcell `000023000320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00002300)))

/-- Subcell `000023000321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00002300)))

/-- Subcell `000023000322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00002300)))

/-- Subcell `000023000323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00002300)))

/-- Subcell `000023000330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00002300)))

/-- Subcell `000023000331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00002300)))

/-- Subcell `000023000332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00002300)))

/-- Subcell `000023000333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023000333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00002300)))

/-- Subcell `000023001220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00002300)))

/-- Subcell `000023001221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00002300)))

/-- Subcell `000023001222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00002300)))

/-- Subcell `000023001223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00002300)))

/-- Subcell `000023001230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaAboveCell00002300)))

/-- Subcell `000023001231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaAboveCell00002300)))

/-- Subcell `000023001232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaAboveCell00002300)))

/-- Subcell `000023001233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaAboveCell00002300)))

/-- Subcell `000023001320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaAboveCell00002300)))

/-- Subcell `000023001321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaAboveCell00002300)))

/-- Subcell `000023001322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaAboveCell00002300)))

/-- Subcell `000023001323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaAboveCell00002300)))

/-- Subcell `000023001330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaAboveCell00002300)))

/-- Subcell `000023001331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaAboveCell00002300)))

/-- Subcell `000023001332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaAboveCell00002300)))

/-- Subcell `000023001333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000023001333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaAboveCell00002300)))

end GerverSofa.PartE.CertificateCells2d2385ed48

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC5TerminalBatchT614400015`.
-/

public section

noncomputable section

section

/-! E24KC5 checkpoint-aware kernel batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2f4f8ea4fc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2f4f8ea4fc

open CertificateCells2f4f8ea4fc
theorem e24KC2ThetaAboveLeaf111123311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112331) = true := by
  have h : ((childLH thetaAboveCell11112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112331) h
theorem e24KC2ThetaAboveLeaf111123312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112331) = true := by
  have h : ((childHL thetaAboveCell11112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112331) h
theorem e24KC2ThetaAboveLeaf111123313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112331) = true := by
  have h : ((childHH thetaAboveCell11112331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112331) h
theorem e24KC2ThetaAboveLeaf111123320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112332) = true := by
  have h : ((childLL thetaAboveCell11112332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112332) h
theorem e24KC2ThetaAboveLeaf111123321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112332) = true := by
  have h : ((childLH thetaAboveCell11112332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112332) h
theorem e24KC2ThetaAboveLeaf111123322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112332) = true := by
  have h : ((childHL thetaAboveCell11112332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112332) h
theorem e24KC2ThetaAboveLeaf111123323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112332) = true := by
  have h : ((childHH thetaAboveCell11112332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112332) h
theorem e24KC2ThetaAboveLeaf111123330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11112333) = true := by
  have h : ((childLL thetaAboveCell11112333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11112333) h
theorem e24KC2ThetaAboveLeaf111123331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11112333) = true := by
  have h : ((childLH thetaAboveCell11112333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11112333) h
theorem e24KC2ThetaAboveLeaf111123332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11112333) = true := by
  have h : ((childHL thetaAboveCell11112333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11112333) h
theorem e24KC2ThetaAboveLeaf111123333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11112333) = true := by
  have h : ((childHH thetaAboveCell11112333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11112333) h
theorem e24KC2ThetaAboveLeaf1111300 :
    adaptiveCoverCheck 12 (childLL (childLL (childHH thetaAboveCell1111))) = true := by
  have h : ((childLL (childLL (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111301 :
    adaptiveCoverCheck 12 (childLH (childLL (childHH thetaAboveCell1111))) = true := by
  have h : ((childLH (childLL (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111302 :
    adaptiveCoverCheck 12 (childHL (childLL (childHH thetaAboveCell1111))) = true := by
  have h : ((childHL (childLL (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111303 :
    adaptiveCoverCheck 12 (childHH (childLL (childHH thetaAboveCell1111))) = true := by
  have h : ((childHH (childLL (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111310 :
    adaptiveCoverCheck 12 (childLL (childLH (childHH thetaAboveCell1111))) = true := by
  have h : ((childLL (childLH (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111311 :
    adaptiveCoverCheck 12 (childLH (childLH (childHH thetaAboveCell1111))) = true := by
  have h : ((childLH (childLH (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111312 :
    adaptiveCoverCheck 12 (childHL (childLH (childHH thetaAboveCell1111))) = true := by
  have h : ((childHL (childLH (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf1111313 :
    adaptiveCoverCheck 12 (childHH (childLH (childHH thetaAboveCell1111))) = true := by
  have h : ((childHH (childLH (childHH thetaAboveCell1111)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childHH thetaAboveCell1111))) h
theorem e24KC2ThetaAboveLeaf11113200 :
    adaptiveCoverCheck 11 thetaAboveCell11113200 = true := by
  have h : (thetaAboveCell11113200).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113200 h
theorem e24KC2ThetaAboveLeaf11113201 :
    adaptiveCoverCheck 11 thetaAboveCell11113201 = true := by
  have h : (thetaAboveCell11113201).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113201 h
theorem e24KC2ThetaAboveLeaf111132020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113202) = true := by
  have h : ((childLL thetaAboveCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113202) h
theorem e24KC2ThetaAboveLeaf111132021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113202) = true := by
  have h : ((childLH thetaAboveCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113202) h
theorem e24KC2ThetaAboveLeaf111132022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113202) = true := by
  have h : ((childHL thetaAboveCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113202) h
theorem e24KC2ThetaAboveLeaf111132023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113202) = true := by
  have h : ((childHH thetaAboveCell11113202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113202) h
theorem e24KC2ThetaAboveLeaf111132030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113203) = true := by
  have h : ((childLL thetaAboveCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113203) h
theorem e24KC2ThetaAboveLeaf111132031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113203) = true := by
  have h : ((childLH thetaAboveCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113203) h
theorem e24KC2ThetaAboveLeaf111132032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113203) = true := by
  have h : ((childHL thetaAboveCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113203) h
theorem e24KC2ThetaAboveLeaf111132033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113203) = true := by
  have h : ((childHH thetaAboveCell11113203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113203) h
theorem e24KC2ThetaAboveLeaf11113210 :
    adaptiveCoverCheck 11 thetaAboveCell11113210 = true := by
  have h : (thetaAboveCell11113210).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113210 h
theorem e24KC2ThetaAboveLeaf11113211 :
    adaptiveCoverCheck 11 thetaAboveCell11113211 = true := by
  have h : (thetaAboveCell11113211).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113211 h
theorem e24KC2ThetaAboveLeaf111132120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113212) = true := by
  have h : ((childLL thetaAboveCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113212) h
theorem e24KC2ThetaAboveLeaf111132121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113212) = true := by
  have h : ((childLH thetaAboveCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113212) h
theorem e24KC2ThetaAboveLeaf111132122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113212) = true := by
  have h : ((childHL thetaAboveCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113212) h
theorem e24KC2ThetaAboveLeaf111132123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113212) = true := by
  have h : ((childHH thetaAboveCell11113212)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113212) h
theorem e24KC2ThetaAboveLeaf111132130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113213) = true := by
  have h : ((childLL thetaAboveCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113213) h
theorem e24KC2ThetaAboveLeaf111132131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113213) = true := by
  have h : ((childLH thetaAboveCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113213) h
theorem e24KC2ThetaAboveLeaf111132132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113213) = true := by
  have h : ((childHL thetaAboveCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113213) h
theorem e24KC2ThetaAboveLeaf111132133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113213) = true := by
  have h : ((childHH thetaAboveCell11113213)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113213) h
theorem e24KC2ThetaAboveLeaf111132200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113220) = true := by
  have h : ((childLL thetaAboveCell11113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113220) h
theorem e24KC2ThetaAboveLeaf111132201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113220) = true := by
  have h : ((childLH thetaAboveCell11113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113220) h
theorem e24KC2ThetaAboveLeaf111132202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113220) = true := by
  have h : ((childHL thetaAboveCell11113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113220) h
theorem e24KC2ThetaAboveLeaf111132203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113220) = true := by
  have h : ((childHH thetaAboveCell11113220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113220) h
theorem e24KC2ThetaAboveLeaf111132210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113221) = true := by
  have h : ((childLL thetaAboveCell11113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113221) h
theorem e24KC2ThetaAboveLeaf111132211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113221) = true := by
  have h : ((childLH thetaAboveCell11113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113221) h
theorem e24KC2ThetaAboveLeaf111132212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113221) = true := by
  have h : ((childHL thetaAboveCell11113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113221) h
theorem e24KC2ThetaAboveLeaf111132213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113221) = true := by
  have h : ((childHH thetaAboveCell11113221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113221) h
theorem e24KC2ThetaAboveLeaf111132220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113222) = true := by
  have h : ((childLL thetaAboveCell11113222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113222) h
theorem e24KC2ThetaAboveLeaf111132221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113222) = true := by
  have h : ((childLH thetaAboveCell11113222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113222) h
theorem e24KC2ThetaAboveLeaf111132222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113222) = true := by
  have h : ((childHL thetaAboveCell11113222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113222) h
theorem e24KC2ThetaAboveLeaf111132223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113222) = true := by
  have h : ((childHH thetaAboveCell11113222)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113222) h
theorem e24KC2ThetaAboveLeaf111132230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113223) = true := by
  have h : ((childLL thetaAboveCell11113223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113223) h
theorem e24KC2ThetaAboveLeaf111132231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113223) = true := by
  have h : ((childLH thetaAboveCell11113223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113223) h
theorem e24KC2ThetaAboveLeaf111132232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113223) = true := by
  have h : ((childHL thetaAboveCell11113223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113223) h
theorem e24KC2ThetaAboveLeaf111132233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113223) = true := by
  have h : ((childHH thetaAboveCell11113223)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113223) h
theorem e24KC2ThetaAboveLeaf111132300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113230) = true := by
  have h : ((childLL thetaAboveCell11113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113230) h
theorem e24KC2ThetaAboveLeaf111132301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113230) = true := by
  have h : ((childLH thetaAboveCell11113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113230) h
theorem e24KC2ThetaAboveLeaf111132302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113230) = true := by
  have h : ((childHL thetaAboveCell11113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113230) h
theorem e24KC2ThetaAboveLeaf111132303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113230) = true := by
  have h : ((childHH thetaAboveCell11113230)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113230) h
theorem e24KC2ThetaAboveLeaf111132310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113231) = true := by
  have h : ((childLL thetaAboveCell11113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113231) h
theorem e24KC2ThetaAboveLeaf111132311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113231) = true := by
  have h : ((childLH thetaAboveCell11113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113231) h
theorem e24KC2ThetaAboveLeaf111132312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113231) = true := by
  have h : ((childHL thetaAboveCell11113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113231) h
theorem e24KC2ThetaAboveLeaf111132313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113231) = true := by
  have h : ((childHH thetaAboveCell11113231)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113231) h
theorem e24KC2ThetaAboveLeaf111132320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113232) = true := by
  have h : ((childLL thetaAboveCell11113232)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113232) h
theorem e24KC2ThetaAboveLeaf111132321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113232) = true := by
  have h : ((childLH thetaAboveCell11113232)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113232) h
theorem e24KC2ThetaAboveLeaf111132322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113232) = true := by
  have h : ((childHL thetaAboveCell11113232)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113232) h
theorem e24KC2ThetaAboveLeaf111132323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113232) = true := by
  have h : ((childHH thetaAboveCell11113232)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113232) h
theorem e24KC2ThetaAboveLeaf111132330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113233) = true := by
  have h : ((childLL thetaAboveCell11113233)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113233) h
theorem e24KC2ThetaAboveLeaf111132331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113233) = true := by
  have h : ((childLH thetaAboveCell11113233)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113233) h
theorem e24KC2ThetaAboveLeaf111132332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113233) = true := by
  have h : ((childHL thetaAboveCell11113233)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113233) h
theorem e24KC2ThetaAboveLeaf111132333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113233) = true := by
  have h : ((childHH thetaAboveCell11113233)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113233) h
theorem e24KC2ThetaAboveLeaf11113300 :
    adaptiveCoverCheck 11 thetaAboveCell11113300 = true := by
  have h : (thetaAboveCell11113300).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113300 h
theorem e24KC2ThetaAboveLeaf11113301 :
    adaptiveCoverCheck 11 thetaAboveCell11113301 = true := by
  have h : (thetaAboveCell11113301).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113301 h
theorem e24KC2ThetaAboveLeaf111133020 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113302) = true := by
  have h : ((childLL thetaAboveCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113302) h
theorem e24KC2ThetaAboveLeaf111133021 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113302) = true := by
  have h : ((childLH thetaAboveCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113302) h
theorem e24KC2ThetaAboveLeaf111133022 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113302) = true := by
  have h : ((childHL thetaAboveCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113302) h
theorem e24KC2ThetaAboveLeaf111133023 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113302) = true := by
  have h : ((childHH thetaAboveCell11113302)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113302) h
theorem e24KC2ThetaAboveLeaf111133030 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113303) = true := by
  have h : ((childLL thetaAboveCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113303) h
theorem e24KC2ThetaAboveLeaf111133031 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113303) = true := by
  have h : ((childLH thetaAboveCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113303) h
theorem e24KC2ThetaAboveLeaf111133032 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113303) = true := by
  have h : ((childHL thetaAboveCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113303) h
theorem e24KC2ThetaAboveLeaf111133033 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113303) = true := by
  have h : ((childHH thetaAboveCell11113303)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113303) h
theorem e24KC2ThetaAboveLeaf11113310 :
    adaptiveCoverCheck 11 thetaAboveCell11113310 = true := by
  have h : (thetaAboveCell11113310).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113310 h
theorem e24KC2ThetaAboveLeaf11113311 :
    adaptiveCoverCheck 11 thetaAboveCell11113311 = true := by
  have h : (thetaAboveCell11113311).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 thetaAboveCell11113311 h
theorem e24KC2ThetaAboveLeaf111133120 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113312) = true := by
  have h : ((childLL thetaAboveCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113312) h
theorem e24KC2ThetaAboveLeaf111133121 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113312) = true := by
  have h : ((childLH thetaAboveCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113312) h
theorem e24KC2ThetaAboveLeaf111133122 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113312) = true := by
  have h : ((childHL thetaAboveCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113312) h
theorem e24KC2ThetaAboveLeaf111133123 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113312) = true := by
  have h : ((childHH thetaAboveCell11113312)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113312) h
theorem e24KC2ThetaAboveLeaf111133130 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113313) = true := by
  have h : ((childLL thetaAboveCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113313) h
theorem e24KC2ThetaAboveLeaf111133131 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113313) = true := by
  have h : ((childLH thetaAboveCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113313) h
theorem e24KC2ThetaAboveLeaf111133132 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113313) = true := by
  have h : ((childHL thetaAboveCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113313) h
theorem e24KC2ThetaAboveLeaf111133133 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113313) = true := by
  have h : ((childHH thetaAboveCell11113313)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113313) h
theorem e24KC2ThetaAboveLeaf111133200 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113320) = true := by
  have h : ((childLL thetaAboveCell11113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113320) h
theorem e24KC2ThetaAboveLeaf111133201 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113320) = true := by
  have h : ((childLH thetaAboveCell11113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113320) h
theorem e24KC2ThetaAboveLeaf111133202 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113320) = true := by
  have h : ((childHL thetaAboveCell11113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113320) h
theorem e24KC2ThetaAboveLeaf111133203 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113320) = true := by
  have h : ((childHH thetaAboveCell11113320)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113320) h
theorem e24KC2ThetaAboveLeaf111133210 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113321) = true := by
  have h : ((childLL thetaAboveCell11113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113321) h
theorem e24KC2ThetaAboveLeaf111133211 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113321) = true := by
  have h : ((childLH thetaAboveCell11113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113321) h
theorem e24KC2ThetaAboveLeaf111133212 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113321) = true := by
  have h : ((childHL thetaAboveCell11113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113321) h
theorem e24KC2ThetaAboveLeaf111133213 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113321) = true := by
  have h : ((childHH thetaAboveCell11113321)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113321) h
theorem e24KC2ThetaAboveLeaf111133220 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113322) = true := by
  have h : ((childLL thetaAboveCell11113322)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113322) h
theorem e24KC2ThetaAboveLeaf111133221 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113322) = true := by
  have h : ((childLH thetaAboveCell11113322)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113322) h
theorem e24KC2ThetaAboveLeaf111133222 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113322) = true := by
  have h : ((childHL thetaAboveCell11113322)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113322) h
theorem e24KC2ThetaAboveLeaf111133223 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113322) = true := by
  have h : ((childHH thetaAboveCell11113322)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113322) h
theorem e24KC2ThetaAboveLeaf111133230 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113323) = true := by
  have h : ((childLL thetaAboveCell11113323)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113323) h
theorem e24KC2ThetaAboveLeaf111133231 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113323) = true := by
  have h : ((childLH thetaAboveCell11113323)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113323) h
theorem e24KC2ThetaAboveLeaf111133232 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113323) = true := by
  have h : ((childHL thetaAboveCell11113323)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113323) h
theorem e24KC2ThetaAboveLeaf111133233 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113323) = true := by
  have h : ((childHH thetaAboveCell11113323)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113323) h
theorem e24KC2ThetaAboveLeaf111133300 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113330) = true := by
  have h : ((childLL thetaAboveCell11113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113330) h
theorem e24KC2ThetaAboveLeaf111133301 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113330) = true := by
  have h : ((childLH thetaAboveCell11113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113330) h
theorem e24KC2ThetaAboveLeaf111133302 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113330) = true := by
  have h : ((childHL thetaAboveCell11113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113330) h
theorem e24KC2ThetaAboveLeaf111133303 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113330) = true := by
  have h : ((childHH thetaAboveCell11113330)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113330) h
theorem e24KC2ThetaAboveLeaf111133310 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113331) = true := by
  have h : ((childLL thetaAboveCell11113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113331) h
theorem e24KC2ThetaAboveLeaf111133311 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113331) = true := by
  have h : ((childLH thetaAboveCell11113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113331) h
theorem e24KC2ThetaAboveLeaf111133312 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113331) = true := by
  have h : ((childHL thetaAboveCell11113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113331) h
theorem e24KC2ThetaAboveLeaf111133313 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113331) = true := by
  have h : ((childHH thetaAboveCell11113331)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113331) h
theorem e24KC2ThetaAboveLeaf111133320 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113332) = true := by
  have h : ((childLL thetaAboveCell11113332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113332) h
theorem e24KC2ThetaAboveLeaf111133321 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113332) = true := by
  have h : ((childLH thetaAboveCell11113332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113332) h
theorem e24KC2ThetaAboveLeaf111133322 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113332) = true := by
  have h : ((childHL thetaAboveCell11113332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113332) h
theorem e24KC2ThetaAboveLeaf111133323 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113332) = true := by
  have h : ((childHH thetaAboveCell11113332)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113332) h
theorem e24KC2ThetaAboveLeaf111133330 :
    adaptiveCoverCheck 10 (childLL thetaAboveCell11113333) = true := by
  have h : ((childLL thetaAboveCell11113333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLL thetaAboveCell11113333) h
theorem e24KC2ThetaAboveLeaf111133331 :
    adaptiveCoverCheck 10 (childLH thetaAboveCell11113333) = true := by
  have h : ((childLH thetaAboveCell11113333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childLH thetaAboveCell11113333) h
theorem e24KC2ThetaAboveLeaf111133332 :
    adaptiveCoverCheck 10 (childHL thetaAboveCell11113333) = true := by
  have h : ((childHL thetaAboveCell11113333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHL thetaAboveCell11113333) h
theorem e24KC2ThetaAboveLeaf111133333 :
    adaptiveCoverCheck 10 (childHH thetaAboveCell11113333) = true := by
  have h : ((childHH thetaAboveCell11113333)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 (childHH thetaAboveCell11113333) h
theorem e24KC2ThetaAboveLeaf1112000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1112))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1112))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1112))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1112))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1112))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1112))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1112))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1112))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf111202 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1112)) = true := by
  have h : ((childHL (childLL thetaAboveCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1112)) h
theorem e24KC2ThetaAboveLeaf111203 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1112)) = true := by
  have h : ((childHH (childLL thetaAboveCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1112)) h
theorem e24KC2ThetaAboveLeaf1112100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1112))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1112))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1112))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1112))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1112))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1112))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1112))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf1112113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1112))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1112)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1112))) h
theorem e24KC2ThetaAboveLeaf111212 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1112)) = true := by
  have h : ((childHL (childLH thetaAboveCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1112)) h
theorem e24KC2ThetaAboveLeaf111213 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1112)) = true := by
  have h : ((childHH (childLH thetaAboveCell1112))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1112)) h
theorem e24KC2ThetaAboveLeaf11122 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1112) = true := by
  have h : ((childHL thetaAboveCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1112) h
theorem e24KC2ThetaAboveLeaf11123 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1112) = true := by
  have h : ((childHH thetaAboveCell1112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1112) h
theorem e24KC2ThetaAboveLeaf1113000 :
    adaptiveCoverCheck 12 (childLL (childLL (childLL thetaAboveCell1113))) = true := by
  have h : ((childLL (childLL (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113001 :
    adaptiveCoverCheck 12 (childLH (childLL (childLL thetaAboveCell1113))) = true := by
  have h : ((childLH (childLL (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113002 :
    adaptiveCoverCheck 12 (childHL (childLL (childLL thetaAboveCell1113))) = true := by
  have h : ((childHL (childLL (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113003 :
    adaptiveCoverCheck 12 (childHH (childLL (childLL thetaAboveCell1113))) = true := by
  have h : ((childHH (childLL (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113010 :
    adaptiveCoverCheck 12 (childLL (childLH (childLL thetaAboveCell1113))) = true := by
  have h : ((childLL (childLH (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113011 :
    adaptiveCoverCheck 12 (childLH (childLH (childLL thetaAboveCell1113))) = true := by
  have h : ((childLH (childLH (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113012 :
    adaptiveCoverCheck 12 (childHL (childLH (childLL thetaAboveCell1113))) = true := by
  have h : ((childHL (childLH (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113013 :
    adaptiveCoverCheck 12 (childHH (childLH (childLL thetaAboveCell1113))) = true := by
  have h : ((childHH (childLH (childLL thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLL thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf111302 :
    adaptiveCoverCheck 13 (childHL (childLL thetaAboveCell1113)) = true := by
  have h : ((childHL (childLL thetaAboveCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLL thetaAboveCell1113)) h
theorem e24KC2ThetaAboveLeaf111303 :
    adaptiveCoverCheck 13 (childHH (childLL thetaAboveCell1113)) = true := by
  have h : ((childHH (childLL thetaAboveCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLL thetaAboveCell1113)) h
theorem e24KC2ThetaAboveLeaf1113100 :
    adaptiveCoverCheck 12 (childLL (childLL (childLH thetaAboveCell1113))) = true := by
  have h : ((childLL (childLL (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113101 :
    adaptiveCoverCheck 12 (childLH (childLL (childLH thetaAboveCell1113))) = true := by
  have h : ((childLH (childLL (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113102 :
    adaptiveCoverCheck 12 (childHL (childLL (childLH thetaAboveCell1113))) = true := by
  have h : ((childHL (childLL (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113103 :
    adaptiveCoverCheck 12 (childHH (childLL (childLH thetaAboveCell1113))) = true := by
  have h : ((childHH (childLL (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113110 :
    adaptiveCoverCheck 12 (childLL (childLH (childLH thetaAboveCell1113))) = true := by
  have h : ((childLL (childLH (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113111 :
    adaptiveCoverCheck 12 (childLH (childLH (childLH thetaAboveCell1113))) = true := by
  have h : ((childLH (childLH (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113112 :
    adaptiveCoverCheck 12 (childHL (childLH (childLH thetaAboveCell1113))) = true := by
  have h : ((childHL (childLH (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf1113113 :
    adaptiveCoverCheck 12 (childHH (childLH (childLH thetaAboveCell1113))) = true := by
  have h : ((childHH (childLH (childLH thetaAboveCell1113)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH (childLH thetaAboveCell1113))) h
theorem e24KC2ThetaAboveLeaf111312 :
    adaptiveCoverCheck 13 (childHL (childLH thetaAboveCell1113)) = true := by
  have h : ((childHL (childLH thetaAboveCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL (childLH thetaAboveCell1113)) h
theorem e24KC2ThetaAboveLeaf111313 :
    adaptiveCoverCheck 13 (childHH (childLH thetaAboveCell1113)) = true := by
  have h : ((childHH (childLH thetaAboveCell1113))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH (childLH thetaAboveCell1113)) h
theorem e24KC2ThetaAboveLeaf11132 :
    adaptiveCoverCheck 14 (childHL thetaAboveCell1113) = true := by
  have h : ((childHL thetaAboveCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHL thetaAboveCell1113) h
theorem e24KC2ThetaAboveLeaf11133 :
    adaptiveCoverCheck 14 (childHH thetaAboveCell1113) = true := by
  have h : ((childHH thetaAboveCell1113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 (childHH thetaAboveCell1113) h
theorem e24KC2ThetaAboveLeaf1120 :
    adaptiveCoverCheck 15 thetaAboveCell1120 = true := by
  have h : (thetaAboveCell1120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1120 h
theorem e24KC2ThetaAboveLeaf1121 :
    adaptiveCoverCheck 15 thetaAboveCell1121 = true := by
  have h : (thetaAboveCell1121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1121 h
theorem e24KC2ThetaAboveLeaf1122 :
    adaptiveCoverCheck 15 thetaAboveCell1122 = true := by
  have h : (thetaAboveCell1122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1122 h
theorem e24KC2ThetaAboveLeaf1123 :
    adaptiveCoverCheck 15 thetaAboveCell1123 = true := by
  have h : (thetaAboveCell1123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1123 h
theorem e24KC2ThetaAboveLeaf1130 :
    adaptiveCoverCheck 15 thetaAboveCell1130 = true := by
  have h : (thetaAboveCell1130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1130 h
theorem e24KC2ThetaAboveLeaf1131 :
    adaptiveCoverCheck 15 thetaAboveCell1131 = true := by
  have h : (thetaAboveCell1131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1131 h
theorem e24KC2ThetaAboveLeaf1132 :
    adaptiveCoverCheck 15 thetaAboveCell1132 = true := by
  have h : (thetaAboveCell1132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1132 h
theorem e24KC2ThetaAboveLeaf1133 :
    adaptiveCoverCheck 15 thetaAboveCell1133 = true := by
  have h : (thetaAboveCell1133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 thetaAboveCell1133 h
theorem e24KC2ThetaAboveLeaf120 :
    adaptiveCoverCheck 16 (childLL (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf121 :
    adaptiveCoverCheck 16 (childLH (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf122 :
    adaptiveCoverCheck 16 (childHL (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHL (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf123 :
    adaptiveCoverCheck 16 (childHH (childHL (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf130 :
    adaptiveCoverCheck 16 (childLL (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf131 :
    adaptiveCoverCheck 16 (childLH (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf132 :
    adaptiveCoverCheck 16 (childHL (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf133 :
    adaptiveCoverCheck 16 (childHH (childHH (childLH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childLH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childLH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf200 :
    adaptiveCoverCheck 16 (childLL (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf201 :
    adaptiveCoverCheck 16 (childLH (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf202 :
    adaptiveCoverCheck 16 (childHL (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf203 :
    adaptiveCoverCheck 16 (childHH (childLL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf210 :
    adaptiveCoverCheck 16 (childLL (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf211 :
    adaptiveCoverCheck 16 (childLH (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf212 :
    adaptiveCoverCheck 16 (childHL (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf213 :
    adaptiveCoverCheck 16 (childHH (childLH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf220 :
    adaptiveCoverCheck 16 (childLL (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf221 :
    adaptiveCoverCheck 16 (childLH (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childHL e24ThetaAboveRoot))) h

theorem e24KC2ThetaAboveLeaf222 :
    adaptiveCoverCheck 16 (childHL (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHL (childHL e24ThetaAboveRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 16 (childHL (childHL (childHL
    e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf223 :
    adaptiveCoverCheck 16 (childHH (childHL (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf230 :
    adaptiveCoverCheck 16 (childLL (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf231 :
    adaptiveCoverCheck 16 (childLH (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf232 :
    adaptiveCoverCheck 16 (childHL (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf233 :
    adaptiveCoverCheck 16 (childHH (childHH (childHL e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childHL e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childHL e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf300 :
    adaptiveCoverCheck 16 (childLL (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf301 :
    adaptiveCoverCheck 16 (childLH (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf302 :
    adaptiveCoverCheck 16 (childHL (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf303 :
    adaptiveCoverCheck 16 (childHH (childLL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf310 :
    adaptiveCoverCheck 16 (childLL (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childLH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf311 :
    adaptiveCoverCheck 16 (childLH (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childLH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf312 :
    adaptiveCoverCheck 16 (childHL (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childLH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf313 :
    adaptiveCoverCheck 16 (childHH (childLH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childLH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childLH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf320 :
    adaptiveCoverCheck 16 (childLL (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf321 :
    adaptiveCoverCheck 16 (childLH (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf322 :
    adaptiveCoverCheck 16 (childHL (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf323 :
    adaptiveCoverCheck 16 (childHH (childHL (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHL (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHL (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf330 :
    adaptiveCoverCheck 16 (childLL (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLL (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLL (childHH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf331 :
    adaptiveCoverCheck 16 (childLH (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childLH (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childLH (childHH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf332 :
    adaptiveCoverCheck 16 (childHL (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHL (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHL (childHH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaAboveLeaf333 :
    adaptiveCoverCheck 16 (childHH (childHH (childHH e24ThetaAboveRoot))) = true := by
  have h : ((childHH (childHH (childHH e24ThetaAboveRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 16 (childHH (childHH (childHH e24ThetaAboveRoot))) h
theorem e24KC2ThetaBelowLeaf0000 :
    adaptiveCoverCheck 14 thetaBelowCell0000 = true := by
  have h : (thetaBelowCell0000).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0000 h
theorem e24KC2ThetaBelowLeaf0001 :
    adaptiveCoverCheck 14 thetaBelowCell0001 = true := by
  have h : (thetaBelowCell0001).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0001 h

theorem e24KC2ThetaBelowLeaf0002 :
    adaptiveCoverCheck 14 thetaBelowCell0002 = true := by
  have h : physicallyIrrelevant thetaBelowCell0002 = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 thetaBelowCell0002 h
theorem e24KC2ThetaBelowLeaf00030 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0003) = true := by
  have h : ((childLL thetaBelowCell0003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0003) h
theorem e24KC2ThetaBelowLeaf00031 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0003) = true := by
  have h : ((childLH thetaBelowCell0003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0003) h

theorem e24KC2ThetaBelowLeaf00032 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0003) = true := by
  have h : physicallyIrrelevant (childHL thetaBelowCell0003) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 13 (childHL thetaBelowCell0003) h
theorem e24KC2ThetaBelowLeaf00033 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0003) = true := by
  have h : ((childHH thetaBelowCell0003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0003) h
theorem e24KC2ThetaBelowLeaf00100 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0010) = true := by
  have h : ((childLL thetaBelowCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0010) h
theorem e24KC2ThetaBelowLeaf00101 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0010) = true := by
  have h : ((childLH thetaBelowCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0010) h
theorem e24KC2ThetaBelowLeaf00102 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0010) = true := by
  have h : ((childHL thetaBelowCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0010) h
theorem e24KC2ThetaBelowLeaf00103 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0010) = true := by
  have h : ((childHH thetaBelowCell0010)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0010) h
theorem e24KC2ThetaBelowLeaf00110 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0011) = true := by
  have h : ((childLL thetaBelowCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0011) h
theorem e24KC2ThetaBelowLeaf00111 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0011) = true := by
  have h : ((childLH thetaBelowCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0011) h
theorem e24KC2ThetaBelowLeaf00112 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0011) = true := by
  have h : ((childHL thetaBelowCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0011) h
theorem e24KC2ThetaBelowLeaf00113 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0011) = true := by
  have h : ((childHH thetaBelowCell0011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0011) h
theorem e24KC2ThetaBelowLeaf00120 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0012) = true := by
  have h : ((childLL thetaBelowCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0012) h
theorem e24KC2ThetaBelowLeaf00121 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0012) = true := by
  have h : ((childLH thetaBelowCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0012) h
theorem e24KC2ThetaBelowLeaf00122 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0012) = true := by
  have h : ((childHL thetaBelowCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0012) h
theorem e24KC2ThetaBelowLeaf00123 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0012) = true := by
  have h : ((childHH thetaBelowCell0012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0012) h
theorem e24KC2ThetaBelowLeaf00130 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0013) = true := by
  have h : ((childLL thetaBelowCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0013) h
theorem e24KC2ThetaBelowLeaf00131 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0013) = true := by
  have h : ((childLH thetaBelowCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0013) h
theorem e24KC2ThetaBelowLeaf00132 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0013) = true := by
  have h : ((childHL thetaBelowCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0013) h
theorem e24KC2ThetaBelowLeaf00133 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0013) = true := by
  have h : ((childHH thetaBelowCell0013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0013) h

theorem e24KC2ThetaBelowLeaf002 :
    adaptiveCoverCheck 15 (childHL (childLL (childLL e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childLL (childLL e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childLL (childLL
    e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf0030 :
    adaptiveCoverCheck 14 thetaBelowCell0030 = true := by
  have h : (thetaBelowCell0030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0030 h
theorem e24KC2ThetaBelowLeaf0031 :
    adaptiveCoverCheck 14 thetaBelowCell0031 = true := by
  have h : (thetaBelowCell0031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0031 h

theorem e24KC2ThetaBelowLeaf0032 :
    adaptiveCoverCheck 14 thetaBelowCell0032 = true := by
  have h : physicallyIrrelevant thetaBelowCell0032 = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 14 thetaBelowCell0032 h
theorem e24KC2ThetaBelowLeaf0033 :
    adaptiveCoverCheck 14 thetaBelowCell0033 = true := by
  have h : (thetaBelowCell0033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0033 h
theorem e24KC2ThetaBelowLeaf01000 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0100) = true := by
  have h : ((childLL thetaBelowCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0100) h
theorem e24KC2ThetaBelowLeaf01001 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0100) = true := by
  have h : ((childLH thetaBelowCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0100) h
theorem e24KC2ThetaBelowLeaf01002 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0100) = true := by
  have h : ((childHL thetaBelowCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0100) h
theorem e24KC2ThetaBelowLeaf01003 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0100) = true := by
  have h : ((childHH thetaBelowCell0100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0100) h
theorem e24KC2ThetaBelowLeaf01010 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0101) = true := by
  have h : ((childLL thetaBelowCell0101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0101) h
theorem e24KC2ThetaBelowLeaf01011 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0101) = true := by
  have h : ((childLH thetaBelowCell0101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0101) h
theorem e24KC2ThetaBelowLeaf01012 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0101) = true := by
  have h : ((childHL thetaBelowCell0101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0101) h
theorem e24KC2ThetaBelowLeaf010130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell0101)) = true := by
  have h : ((childLL (childHH thetaBelowCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH thetaBelowCell0101)) h
theorem e24KC2ThetaBelowLeaf010131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell0101)) = true := by
  have h : ((childLH (childHH thetaBelowCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH thetaBelowCell0101)) h
theorem e24KC2ThetaBelowLeaf010132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell0101)) = true := by
  have h : ((childHL (childHH thetaBelowCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell0101)) h
theorem e24KC2ThetaBelowLeaf010133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell0101)) = true := by
  have h : ((childHH (childHH thetaBelowCell0101))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell0101)) h
theorem e24KC2ThetaBelowLeaf01020 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0102) = true := by
  have h : ((childLL thetaBelowCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0102) h
theorem e24KC2ThetaBelowLeaf01021 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0102) = true := by
  have h : ((childLH thetaBelowCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0102) h
theorem e24KC2ThetaBelowLeaf01022 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0102) = true := by
  have h : ((childHL thetaBelowCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0102) h
theorem e24KC2ThetaBelowLeaf01023 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0102) = true := by
  have h : ((childHH thetaBelowCell0102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0102) h
theorem e24KC2ThetaBelowLeaf01030 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0103) = true := by
  have h : ((childLL thetaBelowCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0103) h
theorem e24KC2ThetaBelowLeaf01031 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0103) = true := by
  have h : ((childLH thetaBelowCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0103) h
theorem e24KC2ThetaBelowLeaf01032 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0103) = true := by
  have h : ((childHL thetaBelowCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0103) h
theorem e24KC2ThetaBelowLeaf01033 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0103) = true := by
  have h : ((childHH thetaBelowCell0103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0103) h
theorem e24KC2ThetaBelowLeaf01100 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0110) = true := by
  have h : ((childLL thetaBelowCell0110)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0110) h
theorem e24KC2ThetaBelowLeaf011010 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell0110)) = true := by
  have h : ((childLL (childLH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011011 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell0110)) = true := by
  have h : ((childLH (childLH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell0110)) = true := by
  have h : ((childHL (childLH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell0110)) = true := by
  have h : ((childHH (childLH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell0110)) = true := by
  have h : ((childLL (childHL thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell0110)) = true := by
  have h : ((childLH (childHL thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell0110)) = true := by
  have h : ((childHL (childHL thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell0110)) = true := by
  have h : ((childHH (childHL thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell0110)) = true := by
  have h : ((childLL (childHH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell0110)) = true := by
  have h : ((childLH (childHH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell0110)) = true := by
  have h : ((childHL (childHH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell0110)) = true := by
  have h : ((childHH (childHH thetaBelowCell0110))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell0110)) h
theorem e24KC2ThetaBelowLeaf011100 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell0111)) = true := by
  have h : ((childLL (childLL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011101 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell0111)) = true := by
  have h : ((childLH (childLL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell0111)) = true := by
  have h : ((childHL (childLL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell0111)) = true := by
  have h : ((childHH (childLL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011110 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell0111)) = true := by
  have h : ((childLL (childLH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011111 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell0111)) = true := by
  have h : ((childLH (childLH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell0111)) = true := by
  have h : ((childHL (childLH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell0111)) = true := by
  have h : ((childHH (childLH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell0111)) = true := by
  have h : ((childLL (childHL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell0111)) = true := by
  have h : ((childLH (childHL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell0111)) = true := by
  have h : ((childHL (childHL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell0111)) = true := by
  have h : ((childHH (childHL thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell0111)) = true := by
  have h : ((childLL (childHH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell0111)) = true := by
  have h : ((childLH (childHH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell0111)) = true := by
  have h : ((childHL (childHH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf011133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell0111)) = true := by
  have h : ((childHH (childHH thetaBelowCell0111))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell0111)) h
theorem e24KC2ThetaBelowLeaf01120 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0112) = true := by
  have h : ((childLL thetaBelowCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0112) h
theorem e24KC2ThetaBelowLeaf01121 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0112) = true := by
  have h : ((childLH thetaBelowCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0112) h
theorem e24KC2ThetaBelowLeaf01122 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0112) = true := by
  have h : ((childHL thetaBelowCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0112) h
theorem e24KC2ThetaBelowLeaf01123 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0112) = true := by
  have h : ((childHH thetaBelowCell0112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0112) h
theorem e24KC2ThetaBelowLeaf01130 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0113) = true := by
  have h : ((childLL thetaBelowCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell0113) h
theorem e24KC2ThetaBelowLeaf01131 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0113) = true := by
  have h : ((childLH thetaBelowCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell0113) h
theorem e24KC2ThetaBelowLeaf01132 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0113) = true := by
  have h : ((childHL thetaBelowCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell0113) h
theorem e24KC2ThetaBelowLeaf01133 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0113) = true := by
  have h : ((childHH thetaBelowCell0113)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell0113) h
theorem e24KC2ThetaBelowLeaf0120 :
    adaptiveCoverCheck 14 thetaBelowCell0120 = true := by
  have h : (thetaBelowCell0120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0120 h
theorem e24KC2ThetaBelowLeaf0121 :
    adaptiveCoverCheck 14 thetaBelowCell0121 = true := by
  have h : (thetaBelowCell0121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0121 h
theorem e24KC2ThetaBelowLeaf0122 :
    adaptiveCoverCheck 14 thetaBelowCell0122 = true := by
  have h : (thetaBelowCell0122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0122 h
theorem e24KC2ThetaBelowLeaf0123 :
    adaptiveCoverCheck 14 thetaBelowCell0123 = true := by
  have h : (thetaBelowCell0123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0123 h
theorem e24KC2ThetaBelowLeaf0130 :
    adaptiveCoverCheck 14 thetaBelowCell0130 = true := by
  have h : (thetaBelowCell0130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0130 h
theorem e24KC2ThetaBelowLeaf0131 :
    adaptiveCoverCheck 14 thetaBelowCell0131 = true := by
  have h : (thetaBelowCell0131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0131 h
theorem e24KC2ThetaBelowLeaf0132 :
    adaptiveCoverCheck 14 thetaBelowCell0132 = true := by
  have h : (thetaBelowCell0132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0132 h
theorem e24KC2ThetaBelowLeaf0133 :
    adaptiveCoverCheck 14 thetaBelowCell0133 = true := by
  have h : (thetaBelowCell0133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell0133 h

theorem e24KC2ThetaBelowLeaf02 :
    adaptiveCoverCheck 16 (childHL (childLL e24ThetaBelowRoot)) = true := by
  have h : physicallyIrrelevant (childHL (childLL e24ThetaBelowRoot)) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 16 (childHL (childLL e24ThetaBelowRoot)) h
theorem e24KC2ThetaBelowLeaf030 :
    adaptiveCoverCheck 15 (childLL (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : ((childLL (childHH (childLL e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLL (childHH (childLL e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf031 :
    adaptiveCoverCheck 15 (childLH (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : ((childLH (childHH (childLL e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childLH (childHH (childLL e24ThetaBelowRoot))) h

theorem e24KC2ThetaBelowLeaf032 :
    adaptiveCoverCheck 15 (childHL (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : physicallyIrrelevant (childHL (childHH (childLL e24ThetaBelowRoot))) = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_physicallyIrrelevant 15 (childHL (childHH (childLL
    e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf033 :
    adaptiveCoverCheck 15 (childHH (childHH (childLL e24ThetaBelowRoot))) = true := by
  have h : ((childHH (childHH (childLL e24ThetaBelowRoot)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 15 (childHH (childHH (childLL e24ThetaBelowRoot))) h
theorem e24KC2ThetaBelowLeaf100000 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1000)) = true := by
  have h : ((childLL (childLL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100001 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1000)) = true := by
  have h : ((childLH (childLL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100002 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1000)) = true := by
  have h : ((childHL (childLL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100003 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1000)) = true := by
  have h : ((childHH (childLL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100010 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1000)) = true := by
  have h : ((childLL (childLH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100011 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1000)) = true := by
  have h : ((childLH (childLH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1000)) = true := by
  have h : ((childHL (childLH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1000)) = true := by
  have h : ((childHH (childLH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1000)) = true := by
  have h : ((childLL (childHL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1000)) = true := by
  have h : ((childLH (childHL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1000)) = true := by
  have h : ((childHL (childHL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1000)) = true := by
  have h : ((childHH (childHL thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1000)) = true := by
  have h : ((childLL (childHH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1000)) = true := by
  have h : ((childLH (childHH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childHH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1000)) = true := by
  have h : ((childHL (childHH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1000)) = true := by
  have h : ((childHH (childHH thetaBelowCell1000))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell1000)) h
theorem e24KC2ThetaBelowLeaf100100 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1001)) = true := by
  have h : ((childLL (childLL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100101 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1001)) = true := by
  have h : ((childLH (childLL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1001)) = true := by
  have h : ((childHL (childLL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1001)) = true := by
  have h : ((childHH (childLL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100110 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1001)) = true := by
  have h : ((childLL (childLH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100111 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1001)) = true := by
  have h : ((childLH (childLH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1001)) = true := by
  have h : ((childHL (childLH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf1001130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH thetaBelowCell1001))) = true := by
  have h : ((childLL (childHH (childLH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH thetaBelowCell1001))) = true := by
  have h : ((childLH (childHH (childLH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1001))) = true := by
  have h : ((childHL (childHH (childLH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1001))) = true := by
  have h : ((childHH (childHH (childLH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf100120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1001)) = true := by
  have h : ((childLL (childHL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childHL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf1001210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1001))) = true := by
  have h : ((childLL (childLH (childHL thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1001))) = true := by
  have h : ((childLH (childLH (childHL thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1001))) = true := by
  have h : ((childHL (childLH (childHL thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHL thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1001))) = true := by
  have h : ((childHH (childLH (childHL thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHL thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf100122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1001)) = true := by
  have h : ((childHL (childHL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1001)) = true := by
  have h : ((childHH (childHL thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf1001300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1001))) = true := by
  have h : ((childLL (childLL (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1001))) = true := by
  have h : ((childLH (childLL (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1001))) = true := by
  have h : ((childHL (childLL (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1001))) = true := by
  have h : ((childHH (childLL (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1001))) = true := by
  have h : ((childLL (childLH (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1001))) = true := by
  have h : ((childLH (childLH (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1001))) = true := by
  have h : ((childHL (childLH (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf1001313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1001))) = true := by
  have h : ((childHH (childLH (childHH thetaBelowCell1001)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHH thetaBelowCell1001))) h
theorem e24KC2ThetaBelowLeaf100132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1001)) = true := by
  have h : ((childHL (childHH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf100133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1001)) = true := by
  have h : ((childHH (childHH thetaBelowCell1001))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHH thetaBelowCell1001)) h
theorem e24KC2ThetaBelowLeaf10020 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1002) = true := by
  have h : ((childLL thetaBelowCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1002) h
theorem e24KC2ThetaBelowLeaf10021 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1002) = true := by
  have h : ((childLH thetaBelowCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLH thetaBelowCell1002) h
theorem e24KC2ThetaBelowLeaf10022 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1002) = true := by
  have h : ((childHL thetaBelowCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1002) h
theorem e24KC2ThetaBelowLeaf10023 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1002) = true := by
  have h : ((childHH thetaBelowCell1002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1002) h
theorem e24KC2ThetaBelowLeaf10030 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1003) = true := by
  have h : ((childLL thetaBelowCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childLL thetaBelowCell1003) h
theorem e24KC2ThetaBelowLeaf100310 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1003)) = true := by
  have h : ((childLL (childLH thetaBelowCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1003)) h
theorem e24KC2ThetaBelowLeaf100311 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1003)) = true := by
  have h : ((childLH (childLH thetaBelowCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1003)) h
theorem e24KC2ThetaBelowLeaf100312 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1003)) = true := by
  have h : ((childHL (childLH thetaBelowCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1003)) h
theorem e24KC2ThetaBelowLeaf100313 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1003)) = true := by
  have h : ((childHH (childLH thetaBelowCell1003))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1003)) h
theorem e24KC2ThetaBelowLeaf10032 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1003) = true := by
  have h : ((childHL thetaBelowCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1003) h
theorem e24KC2ThetaBelowLeaf10033 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1003) = true := by
  have h : ((childHH thetaBelowCell1003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1003) h
theorem e24KC2ThetaBelowLeaf101000 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1010)) = true := by
  have h : ((childLL (childLL thetaBelowCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1010)) h
theorem e24KC2ThetaBelowLeaf1010010 :
    adaptiveCoverCheck 11 (childLL (childLH (childLL thetaBelowCell1010))) = true := by
  have h : ((childLL (childLH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010011 :
    adaptiveCoverCheck 11 (childLH (childLH (childLL thetaBelowCell1010))) = true := by
  have h : ((childLH (childLH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010012 :
    adaptiveCoverCheck 11 (childHL (childLH (childLL thetaBelowCell1010))) = true := by
  have h : ((childHL (childLH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010013 :
    adaptiveCoverCheck 11 (childHH (childLH (childLL thetaBelowCell1010))) = true := by
  have h : ((childHH (childLH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL thetaBelowCell1010))) = true := by
  have h : ((childLL (childHL (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL thetaBelowCell1010))) = true := by
  have h : ((childLH (childHL (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1010))) = true := by
  have h : ((childHL (childHL (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1010))) = true := by
  have h : ((childHH (childHL (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL thetaBelowCell1010))) = true := by
  have h : ((childLL (childHH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL thetaBelowCell1010))) = true := by
  have h : ((childLH (childHH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1010))) = true := by
  have h : ((childHL (childHH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1010))) = true := by
  have h : ((childHH (childHH (childLL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010100 :
    adaptiveCoverCheck 11 (childLL (childLL (childLH thetaBelowCell1010))) = true := by
  have h : ((childLL (childLL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010101 :
    adaptiveCoverCheck 11 (childLH (childLL (childLH thetaBelowCell1010))) = true := by
  have h : ((childLH (childLL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010102 :
    adaptiveCoverCheck 11 (childHL (childLL (childLH thetaBelowCell1010))) = true := by
  have h : ((childHL (childLL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010103 :
    adaptiveCoverCheck 11 (childHH (childLL (childLH thetaBelowCell1010))) = true := by
  have h : ((childHH (childLL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010110 :
    adaptiveCoverCheck 11 (childLL (childLH (childLH thetaBelowCell1010))) = true := by
  have h : ((childLL (childLH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010111 :
    adaptiveCoverCheck 11 (childLH (childLH (childLH thetaBelowCell1010))) = true := by
  have h : ((childLH (childLH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010112 :
    adaptiveCoverCheck 11 (childHL (childLH (childLH thetaBelowCell1010))) = true := by
  have h : ((childHL (childLH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010113 :
    adaptiveCoverCheck 11 (childHH (childLH (childLH thetaBelowCell1010))) = true := by
  have h : ((childHH (childLH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH thetaBelowCell1010))) = true := by
  have h : ((childLL (childHL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH thetaBelowCell1010))) = true := by
  have h : ((childLH (childHL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1010))) = true := by
  have h : ((childHL (childHL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1010))) = true := by
  have h : ((childHH (childHL (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH thetaBelowCell1010))) = true := by
  have h : ((childLL (childHH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH thetaBelowCell1010))) = true := by
  have h : ((childLH (childHH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1010))) = true := by
  have h : ((childHL (childHH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1010))) = true := by
  have h : ((childHH (childHH (childLH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1010))) = true := by
  have h : ((childLL (childLL (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1010))) = true := by
  have h : ((childLH (childLL (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1010))) = true := by
  have h : ((childHL (childLL (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1010))) = true := by
  have h : ((childHH (childLL (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1010))) = true := by
  have h : ((childLL (childLH (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1010))) = true := by
  have h : ((childLH (childLH (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1010))) = true := by
  have h : ((childHL (childLH (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1010))) = true := by
  have h : ((childHH (childLH (childHL thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHL thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf101022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1010)) = true := by
  have h : ((childHL (childHL thetaBelowCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childHL thetaBelowCell1010)) h
theorem e24KC2ThetaBelowLeaf101023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1010)) = true := by
  have h : ((childHH (childHL thetaBelowCell1010))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childHL thetaBelowCell1010)) h
theorem e24KC2ThetaBelowLeaf1010300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1010))) = true := by
  have h : ((childLL (childLL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1010))) = true := by
  have h : ((childLH (childLL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1010))) = true := by
  have h : ((childHL (childLL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1010))) = true := by
  have h : ((childHH (childLL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1010))) = true := by
  have h : ((childLL (childLH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1010))) = true := by
  have h : ((childLH (childLH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1010))) = true := by
  have h : ((childHL (childLH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1010))) = true := by
  have h : ((childHH (childLH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1010))) = true := by
  have h : ((childLL (childHL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1010))) = true := by
  have h : ((childLH (childHL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1010))) = true := by
  have h : ((childHL (childHL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1010))) = true := by
  have h : ((childHH (childHL (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1010))) = true := by
  have h : ((childLL (childHH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1010))) = true := by
  have h : ((childLH (childHH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1010))) = true := by
  have h : ((childHL (childHH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1010333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1010))) = true := by
  have h : ((childHH (childHH (childHH thetaBelowCell1010)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH thetaBelowCell1010))) h
theorem e24KC2ThetaBelowLeaf1011000 :
    adaptiveCoverCheck 11 (childLL (childLL (childLL thetaBelowCell1011))) = true := by
  have h : ((childLL (childLL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011001 :
    adaptiveCoverCheck 11 (childLH (childLL (childLL thetaBelowCell1011))) = true := by
  have h : ((childLH (childLL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011002 :
    adaptiveCoverCheck 11 (childHL (childLL (childLL thetaBelowCell1011))) = true := by
  have h : ((childHL (childLL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011003 :
    adaptiveCoverCheck 11 (childHH (childLL (childLL thetaBelowCell1011))) = true := by
  have h : ((childHH (childLL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf101101 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1011)) = true := by
  have h : ((childLH (childLL thetaBelowCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1011)) h
theorem e24KC2ThetaBelowLeaf1011020 :
    adaptiveCoverCheck 11 (childLL (childHL (childLL thetaBelowCell1011))) = true := by
  have h : ((childLL (childHL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011021 :
    adaptiveCoverCheck 11 (childLH (childHL (childLL thetaBelowCell1011))) = true := by
  have h : ((childLH (childHL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1011))) = true := by
  have h : ((childHL (childHL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1011))) = true := by
  have h : ((childHH (childHL (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011030 :
    adaptiveCoverCheck 11 (childLL (childHH (childLL thetaBelowCell1011))) = true := by
  have h : ((childLL (childHH (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011031 :
    adaptiveCoverCheck 11 (childLH (childHH (childLL thetaBelowCell1011))) = true := by
  have h : ((childLH (childHH (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1011))) = true := by
  have h : ((childHL (childHH (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1011))) = true := by
  have h : ((childHH (childHH (childLL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf101110 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1011)) = true := by
  have h : ((childLL (childLH thetaBelowCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1011)) h
theorem e24KC2ThetaBelowLeaf101111 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1011)) = true := by
  have h : ((childLH (childLH thetaBelowCell1011))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1011)) h
theorem e24KC2ThetaBelowLeaf1011120 :
    adaptiveCoverCheck 11 (childLL (childHL (childLH thetaBelowCell1011))) = true := by
  have h : ((childLL (childHL (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011121 :
    adaptiveCoverCheck 11 (childLH (childHL (childLH thetaBelowCell1011))) = true := by
  have h : ((childLH (childHL (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1011))) = true := by
  have h : ((childHL (childHL (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1011))) = true := by
  have h : ((childHH (childHL (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011130 :
    adaptiveCoverCheck 11 (childLL (childHH (childLH thetaBelowCell1011))) = true := by
  have h : ((childLL (childHH (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011131 :
    adaptiveCoverCheck 11 (childLH (childHH (childLH thetaBelowCell1011))) = true := by
  have h : ((childLH (childHH (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1011))) = true := by
  have h : ((childHL (childHH (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1011))) = true := by
  have h : ((childHH (childHH (childLH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childLH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1011))) = true := by
  have h : ((childLL (childLL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1011))) = true := by
  have h : ((childLH (childLL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1011))) = true := by
  have h : ((childHL (childLL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1011))) = true := by
  have h : ((childHH (childLL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1011))) = true := by
  have h : ((childLL (childLH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1011))) = true := by
  have h : ((childLH (childLH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1011))) = true := by
  have h : ((childHL (childLH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1011))) = true := by
  have h : ((childHH (childLH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childLH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL thetaBelowCell1011))) = true := by
  have h : ((childLL (childHL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL thetaBelowCell1011))) = true := by
  have h : ((childLH (childHL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL thetaBelowCell1011))) = true := by
  have h : ((childHL (childHL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL thetaBelowCell1011))) = true := by
  have h : ((childHH (childHL (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL thetaBelowCell1011))) = true := by
  have h : ((childLL (childHH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL thetaBelowCell1011))) = true := by
  have h : ((childLH (childHH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL thetaBelowCell1011))) = true := by
  have h : ((childHL (childHH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL thetaBelowCell1011))) = true := by
  have h : ((childHH (childHH (childHL thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHL thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1011))) = true := by
  have h : ((childLL (childLL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1011))) = true := by
  have h : ((childLH (childLL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childLL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1011))) = true := by
  have h : ((childHL (childLL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childLL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf10113030 :
    adaptiveCoverCheck 10 thetaBelowCell10113030 = true := by
  have h : (thetaBelowCell10113030).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113030 h
theorem e24KC2ThetaBelowLeaf10113031 :
    adaptiveCoverCheck 10 thetaBelowCell10113031 = true := by
  have h : (thetaBelowCell10113031).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113031 h
theorem e24KC2ThetaBelowLeaf10113032 :
    adaptiveCoverCheck 10 thetaBelowCell10113032 = true := by
  have h : (thetaBelowCell10113032).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113032 h
theorem e24KC2ThetaBelowLeaf10113033 :
    adaptiveCoverCheck 10 thetaBelowCell10113033 = true := by
  have h : (thetaBelowCell10113033).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113033 h
theorem e24KC2ThetaBelowLeaf1011310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1011))) = true := by
  have h : ((childLL (childLH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childLH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf10113110 :
    adaptiveCoverCheck 10 thetaBelowCell10113110 = true := by
  have h : (thetaBelowCell10113110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113110 h
theorem e24KC2ThetaBelowLeaf10113111 :
    adaptiveCoverCheck 10 thetaBelowCell10113111 = true := by
  have h : (thetaBelowCell10113111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113111 h
theorem e24KC2ThetaBelowLeaf10113112 :
    adaptiveCoverCheck 10 thetaBelowCell10113112 = true := by
  have h : (thetaBelowCell10113112).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113112 h
theorem e24KC2ThetaBelowLeaf10113113 :
    adaptiveCoverCheck 10 thetaBelowCell10113113 = true := by
  have h : (thetaBelowCell10113113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113113 h
theorem e24KC2ThetaBelowLeaf10113120 :
    adaptiveCoverCheck 10 thetaBelowCell10113120 = true := by
  have h : (thetaBelowCell10113120).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113120 h
theorem e24KC2ThetaBelowLeaf10113121 :
    adaptiveCoverCheck 10 thetaBelowCell10113121 = true := by
  have h : (thetaBelowCell10113121).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113121 h
theorem e24KC2ThetaBelowLeaf10113122 :
    adaptiveCoverCheck 10 thetaBelowCell10113122 = true := by
  have h : (thetaBelowCell10113122).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113122 h
theorem e24KC2ThetaBelowLeaf10113123 :
    adaptiveCoverCheck 10 thetaBelowCell10113123 = true := by
  have h : (thetaBelowCell10113123).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113123 h
theorem e24KC2ThetaBelowLeaf10113130 :
    adaptiveCoverCheck 10 thetaBelowCell10113130 = true := by
  have h : (thetaBelowCell10113130).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113130 h
theorem e24KC2ThetaBelowLeaf10113131 :
    adaptiveCoverCheck 10 thetaBelowCell10113131 = true := by
  have h : (thetaBelowCell10113131).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113131 h
theorem e24KC2ThetaBelowLeaf10113132 :
    adaptiveCoverCheck 10 thetaBelowCell10113132 = true := by
  have h : (thetaBelowCell10113132).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113132 h
theorem e24KC2ThetaBelowLeaf10113133 :
    adaptiveCoverCheck 10 thetaBelowCell10113133 = true := by
  have h : (thetaBelowCell10113133).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 thetaBelowCell10113133 h
theorem e24KC2ThetaBelowLeaf1011320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1011))) = true := by
  have h : ((childLL (childHL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1011))) = true := by
  have h : ((childLH (childHL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1011))) = true := by
  have h : ((childHL (childHL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1011))) = true := by
  have h : ((childHH (childHL (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHL (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1011))) = true := by
  have h : ((childLL (childHH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLL (childHH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1011))) = true := by
  have h : ((childLH (childHH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childLH (childHH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1011))) = true := by
  have h : ((childHL (childHH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHL (childHH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf1011333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1011))) = true := by
  have h : ((childHH (childHH (childHH thetaBelowCell1011)))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 11 (childHH (childHH (childHH thetaBelowCell1011))) h
theorem e24KC2ThetaBelowLeaf101200 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1012)) = true := by
  have h : ((childLL (childLL thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101201 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1012)) = true := by
  have h : ((childLH (childLL thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101202 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1012)) = true := by
  have h : ((childHL (childLL thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101203 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1012)) = true := by
  have h : ((childHH (childLL thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101210 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1012)) = true := by
  have h : ((childLL (childLH thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101211 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1012)) = true := by
  have h : ((childLH (childLH thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101212 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1012)) = true := by
  have h : ((childHL (childLH thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf101213 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1012)) = true := by
  have h : ((childHH (childLH thetaBelowCell1012))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1012)) h
theorem e24KC2ThetaBelowLeaf10122 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1012) = true := by
  have h : ((childHL thetaBelowCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1012) h
theorem e24KC2ThetaBelowLeaf10123 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1012) = true := by
  have h : ((childHH thetaBelowCell1012)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1012) h
theorem e24KC2ThetaBelowLeaf101300 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1013)) = true := by
  have h : ((childLL (childLL thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLL thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101301 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1013)) = true := by
  have h : ((childLH (childLL thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLL thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101302 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1013)) = true := by
  have h : ((childHL (childLL thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLL thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101303 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1013)) = true := by
  have h : ((childHH (childLL thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLL thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101310 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1013)) = true := by
  have h : ((childLL (childLH thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLL (childLH thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101311 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1013)) = true := by
  have h : ((childLH (childLH thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childLH (childLH thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101312 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1013)) = true := by
  have h : ((childHL (childLH thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHL (childLH thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf101313 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1013)) = true := by
  have h : ((childHH (childLH thetaBelowCell1013))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 12 (childHH (childLH thetaBelowCell1013)) h
theorem e24KC2ThetaBelowLeaf10132 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1013) = true := by
  have h : ((childHL thetaBelowCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHL thetaBelowCell1013) h
theorem e24KC2ThetaBelowLeaf10133 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1013) = true := by
  have h : ((childHH thetaBelowCell1013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 13 (childHH thetaBelowCell1013) h
theorem e24KC2ThetaBelowLeaf1020 :
    adaptiveCoverCheck 14 thetaBelowCell1020 = true := by
  have h : (thetaBelowCell1020).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1020 h
theorem e24KC2ThetaBelowLeaf1021 :
    adaptiveCoverCheck 14 thetaBelowCell1021 = true := by
  have h : (thetaBelowCell1021).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1021 h
theorem e24KC2ThetaBelowLeaf1022 :
    adaptiveCoverCheck 14 thetaBelowCell1022 = true := by
  have h : (thetaBelowCell1022).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 14 thetaBelowCell1022 h

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

* `KernelOnly.PartE.E24KC6ProofBatch11b2bedf1dcd3516`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2d2385ed48

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells2d2385ed48

open CertificateCells2d2385ed48
theorem cover_subtree_edb64f01a0c6 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103100)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022103100))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022103100))) h))
    (by
      have h : ((childLH (childHL thetaAboveCell000022103100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022103100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103100))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103100))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103100))) h))

theorem cover_subtree_a40a1df9b3a1 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103100)
    (by
      have h : ((childLL (childHH thetaAboveCell000022103100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022103100)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022103100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022103100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103100))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103100))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103100))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103100))) h))

theorem cover_subtree_e870c75d402b :
    adaptiveCoverCheck 7 thetaAboveCell000022103100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103100
    (by
      have h : ((childLL thetaAboveCell000022103100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103100) h)
    (by
      have h : ((childLH thetaAboveCell000022103100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103100) h)
    cover_subtree_edb64f01a0c6
    cover_subtree_a40a1df9b3a1

theorem cover_subtree_5efea1d56268 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103101)
    (by
      have h : ((childLL (childHL thetaAboveCell000022103101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022103101)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022103101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022103101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103101))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103101))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103101))) h))

theorem cover_subtree_d2aa99fffe31 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103101)
    (by
      have h : ((childLL (childHH thetaAboveCell000022103101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022103101)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022103101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022103101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103101))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103101))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103101))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103101))) h))

theorem cover_subtree_0abbf33fdebf :
    adaptiveCoverCheck 7 thetaAboveCell000022103101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103101
    (by
      have h : ((childLL thetaAboveCell000022103101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103101) h)
    (by
      have h : ((childLH thetaAboveCell000022103101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103101) h)
    cover_subtree_5efea1d56268
    cover_subtree_d2aa99fffe31

theorem cover_subtree_1d0945e98034 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103102))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103102))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103102))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103102)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103102)) h)

theorem cover_subtree_e19e97fa44f4 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103102))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103102))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103102))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103102))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103102)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103102)) h)

theorem cover_subtree_92cf9ed4da50 :
    adaptiveCoverCheck 7 thetaAboveCell000022103102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103102
    cover_subtree_1d0945e98034
    cover_subtree_e19e97fa44f4
    (by
      have h : ((childHL thetaAboveCell000022103102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103102) h)
    (by
      have h : ((childHH thetaAboveCell000022103102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103102) h)

theorem cover_subtree_637f019f84f2 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103103))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103103))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103103))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103103)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103103)) h)

theorem cover_subtree_2f9a3a39c9a5 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103103))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103103))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103103))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103103))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103103)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103103)) h)

theorem cover_subtree_30350e948f84 :
    adaptiveCoverCheck 7 thetaAboveCell000022103103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103103
    cover_subtree_637f019f84f2
    cover_subtree_2f9a3a39c9a5
    (by
      have h : ((childHL thetaAboveCell000022103103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103103) h)
    (by
      have h : ((childHH thetaAboveCell000022103103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103103) h)

theorem cover_subtree_4a228fe99e26 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002210)))
    cover_subtree_e870c75d402b
    cover_subtree_0abbf33fdebf
    cover_subtree_92cf9ed4da50
    cover_subtree_30350e948f84

theorem cover_subtree_dec56845b136 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103110)
    (by
      have h : ((childLL (childHL thetaAboveCell000022103110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022103110)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022103110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022103110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103110))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103110))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103110))) h))

theorem cover_subtree_6de59f8bb098 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103110)
    (by
      have h : ((childLL (childHH thetaAboveCell000022103110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022103110)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022103110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022103110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103110))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103110))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103110))) h))

theorem cover_subtree_ab36c8726f5a :
    adaptiveCoverCheck 7 thetaAboveCell000022103110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103110
    (by
      have h : ((childLL thetaAboveCell000022103110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103110) h)
    (by
      have h : ((childLH thetaAboveCell000022103110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103110) h)
    cover_subtree_dec56845b136
    cover_subtree_6de59f8bb098

theorem cover_subtree_59e28493c6fc :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103111)
    (by
      have h : ((childLL (childHL thetaAboveCell000022103111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022103111)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022103111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022103111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103111))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103111))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103111))) h))

theorem cover_subtree_de44712e43a7 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103111)
    (by
      have h : ((childLL (childHH thetaAboveCell000022103111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022103111)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022103111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022103111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103111))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103111))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103111))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103111))) h))

theorem cover_subtree_526ec4bd5c8b :
    adaptiveCoverCheck 7 thetaAboveCell000022103111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103111
    (by
      have h : ((childLL thetaAboveCell000022103111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103111) h)
    (by
      have h : ((childLH thetaAboveCell000022103111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103111) h)
    cover_subtree_59e28493c6fc
    cover_subtree_de44712e43a7

theorem cover_subtree_f14f28c14e3c :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103112))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103112))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103112))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103112)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103112)) h)

theorem cover_subtree_2e18124844df :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103112))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103112))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103112))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103112))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103112)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103112)) h)

theorem cover_subtree_f0199f1a57d7 :
    adaptiveCoverCheck 7 thetaAboveCell000022103112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103112
    cover_subtree_f14f28c14e3c
    cover_subtree_2e18124844df
    (by
      have h : ((childHL thetaAboveCell000022103112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103112) h)
    (by
      have h : ((childHH thetaAboveCell000022103112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103112) h)

theorem cover_subtree_48a3af012806 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103113))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103113))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103113))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103113)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103113)) h)

theorem cover_subtree_e9c96ebadfa8 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103113))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103113))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103113))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103113))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103113)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103113)) h)

theorem cover_subtree_88cc51539fac :
    adaptiveCoverCheck 7 thetaAboveCell000022103113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103113
    cover_subtree_48a3af012806
    cover_subtree_e9c96ebadfa8
    (by
      have h : ((childHL thetaAboveCell000022103113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103113) h)
    (by
      have h : ((childHH thetaAboveCell000022103113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103113) h)

theorem cover_subtree_a1d8aa321d27 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002210)))
    cover_subtree_ab36c8726f5a
    cover_subtree_526ec4bd5c8b
    cover_subtree_f0199f1a57d7
    cover_subtree_88cc51539fac

theorem e24KC2ThetaAboveLeaf0000221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002210))
    cover_subtree_4a228fe99e26
    cover_subtree_a1d8aa321d27
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103120 h)
        (by
          have h : (thetaAboveCell000022103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103121 h)
        (by
          have h : (thetaAboveCell000022103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103122 h)
        (by
          have h : (thetaAboveCell000022103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103130 h)
        (by
          have h : (thetaAboveCell000022103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103131 h)
        (by
          have h : (thetaAboveCell000022103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103132 h)
        (by
          have h : (thetaAboveCell000022103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103133 h))
theorem e24KC2ThetaAboveLeaf0000221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002210))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002210))) h)
theorem e24KC2ThetaAboveLeaf0000221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002210))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002210))) h)
theorem e24KC2ThetaAboveLeaf0000221102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00002211))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00002211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022110220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110220 h)
        (by
          have h : (thetaAboveCell000022110221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110221 h)
        (by
          have h : (thetaAboveCell000022110222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110222 h)
        (by
          have h : (thetaAboveCell000022110223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022110230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110230 h)
        (by
          have h : (thetaAboveCell000022110231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110231 h)
        (by
          have h : (thetaAboveCell000022110232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110232 h)
        (by
          have h : (thetaAboveCell000022110233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110233 h))
theorem e24KC2ThetaAboveLeaf0000221103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00002211))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00002211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022110320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110320 h)
        (by
          have h : (thetaAboveCell000022110321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110321 h)
        (by
          have h : (thetaAboveCell000022110322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110322 h)
        (by
          have h : (thetaAboveCell000022110323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022110330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110330 h)
        (by
          have h : (thetaAboveCell000022110331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110331 h)
        (by
          have h : (thetaAboveCell000022110332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110332 h)
        (by
          have h : (thetaAboveCell000022110333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022110333 h))
theorem e24KC2ThetaAboveLeaf0000221112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00002211))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00002211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022111220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111220 h)
        (by
          have h : (thetaAboveCell000022111221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111221 h)
        (by
          have h : (thetaAboveCell000022111222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111222 h)
        (by
          have h : (thetaAboveCell000022111223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022111230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111230 h)
        (by
          have h : (thetaAboveCell000022111231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111231 h)
        (by
          have h : (thetaAboveCell000022111232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111232 h)
        (by
          have h : (thetaAboveCell000022111233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111233 h))
theorem e24KC2ThetaAboveLeaf0000221113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00002211))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00002211))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022111320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111320 h)
        (by
          have h : (thetaAboveCell000022111321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111321 h)
        (by
          have h : (thetaAboveCell000022111322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111322 h)
        (by
          have h : (thetaAboveCell000022111323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022111330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111330 h)
        (by
          have h : (thetaAboveCell000022111331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111331 h)
        (by
          have h : (thetaAboveCell000022111332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111332 h)
        (by
          have h : (thetaAboveCell000022111333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022111333 h))
theorem cover_subtree_43fd6107c581 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112000)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112000)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112000))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112000))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112000))) h))

theorem cover_subtree_2f5d0def195d :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112000)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112000)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112000))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112000))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112000))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112000))) h))

theorem cover_subtree_b847b0feac2d :
    adaptiveCoverCheck 7 thetaAboveCell000022112000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112000
    (by
      have h : ((childLL thetaAboveCell000022112000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112000) h)
    (by
      have h : ((childLH thetaAboveCell000022112000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112000) h)
    cover_subtree_43fd6107c581
    cover_subtree_2f5d0def195d

theorem cover_subtree_4950fac9bab9 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112001)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112001)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112001))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112001))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112001))) h))

theorem cover_subtree_0e72524614ed :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112001)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112001)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112001))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112001))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112001))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112001))) h))

theorem cover_subtree_b10e2b341d50 :
    adaptiveCoverCheck 7 thetaAboveCell000022112001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112001
    (by
      have h : ((childLL thetaAboveCell000022112001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112001) h)
    (by
      have h : ((childLH thetaAboveCell000022112001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112001) h)
    cover_subtree_4950fac9bab9
    cover_subtree_0e72524614ed

theorem cover_subtree_76b490d87a4e :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112002))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112002))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112002))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112002)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112002)) h)

theorem cover_subtree_4b9c90d07695 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112002))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112002))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112002))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112002))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112002)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022112002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022112002)) h)

theorem cover_subtree_b7dd7162f0b9 :
    adaptiveCoverCheck 7 thetaAboveCell000022112002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112002
    cover_subtree_76b490d87a4e
    cover_subtree_4b9c90d07695
    (by
      have h : ((childHL thetaAboveCell000022112002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112002) h)
    (by
      have h : ((childHH thetaAboveCell000022112002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112002) h)

theorem cover_subtree_de29b5c5a11d :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112003))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112003))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112003))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112003)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112003)) h)

theorem cover_subtree_31f4d5809705 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112003))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112003))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112003))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112003))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112003)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022112003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022112003)) h)

theorem cover_subtree_c9c566e964a9 :
    adaptiveCoverCheck 7 thetaAboveCell000022112003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112003
    cover_subtree_de29b5c5a11d
    cover_subtree_31f4d5809705
    (by
      have h : ((childHL thetaAboveCell000022112003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112003) h)
    (by
      have h : ((childHH thetaAboveCell000022112003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112003) h)

theorem cover_subtree_da67754fe633 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002211)))
    cover_subtree_b847b0feac2d
    cover_subtree_b10e2b341d50
    cover_subtree_b7dd7162f0b9
    cover_subtree_c9c566e964a9

theorem cover_subtree_95f6e6d97c24 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112010)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112010)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112010))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112010))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112010))) h))

theorem cover_subtree_9c844972ea1f :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112010)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112010)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112010))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112010))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112010))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112010))) h))

theorem cover_subtree_04ff1f51c7c8 :
    adaptiveCoverCheck 7 thetaAboveCell000022112010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112010
    (by
      have h : ((childLL thetaAboveCell000022112010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112010) h)
    (by
      have h : ((childLH thetaAboveCell000022112010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112010) h)
    cover_subtree_95f6e6d97c24
    cover_subtree_9c844972ea1f

theorem cover_subtree_754b681a3e26 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112011)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112011)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112011))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112011))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112011))) h))

theorem cover_subtree_497a7c55810a :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112011)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112011)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112011))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112011))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112011))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112011))) h))

theorem cover_subtree_92922a2edd2b :
    adaptiveCoverCheck 7 thetaAboveCell000022112011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112011
    (by
      have h : ((childLL thetaAboveCell000022112011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112011) h)
    (by
      have h : ((childLH thetaAboveCell000022112011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112011) h)
    cover_subtree_754b681a3e26
    cover_subtree_497a7c55810a

theorem cover_subtree_bfdd630a1f02 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112012))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112012))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112012))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112012)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112012)) h)

theorem cover_subtree_d41a2b9225dd :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112012))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112012))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112012))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112012))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112012)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022112012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022112012)) h)

theorem cover_subtree_b54fc51b3ec8 :
    adaptiveCoverCheck 7 thetaAboveCell000022112012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112012
    cover_subtree_bfdd630a1f02
    cover_subtree_d41a2b9225dd
    (by
      have h : ((childHL thetaAboveCell000022112012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112012) h)
    (by
      have h : ((childHH thetaAboveCell000022112012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112012) h)

theorem cover_subtree_1ae8b8609603 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112013))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112013))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112013))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112013)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112013)) h)

theorem cover_subtree_254e7d6a1a8d :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112013))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112013))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112013))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112013))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112013)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022112013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022112013)) h)

theorem cover_subtree_316108a366aa :
    adaptiveCoverCheck 7 thetaAboveCell000022112013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112013
    cover_subtree_1ae8b8609603
    cover_subtree_254e7d6a1a8d
    (by
      have h : ((childHL thetaAboveCell000022112013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112013) h)
    (by
      have h : ((childHH thetaAboveCell000022112013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112013) h)

theorem cover_subtree_23a35d53c9e2 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00002211)))
    cover_subtree_04ff1f51c7c8
    cover_subtree_92922a2edd2b
    cover_subtree_b54fc51b3ec8
    cover_subtree_316108a366aa

theorem e24KC2ThetaAboveLeaf0000221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00002211))
    cover_subtree_da67754fe633
    cover_subtree_23a35d53c9e2
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112020 h)
        (by
          have h : (thetaAboveCell000022112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112021 h)
        (by
          have h : (thetaAboveCell000022112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112022 h)
        (by
          have h : (thetaAboveCell000022112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112030 h)
        (by
          have h : (thetaAboveCell000022112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112031 h)
        (by
          have h : (thetaAboveCell000022112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112032 h)
        (by
          have h : (thetaAboveCell000022112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112033 h))
theorem cover_subtree_021e44d85b50 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112100)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112100)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112100))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112100))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112100))) h))

theorem cover_subtree_62fa6c2e1429 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112100)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112100)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112100))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112100))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112100))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112100))) h))

theorem cover_subtree_ff28352fdcbd :
    adaptiveCoverCheck 7 thetaAboveCell000022112100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112100
    (by
      have h : ((childLL thetaAboveCell000022112100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112100) h)
    (by
      have h : ((childLH thetaAboveCell000022112100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112100) h)
    cover_subtree_021e44d85b50
    cover_subtree_62fa6c2e1429

theorem cover_subtree_4284ed2ee8d6 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112101)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112101)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112101))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112101))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112101))) h))

theorem cover_subtree_21c449726701 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112101)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112101)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112101))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112101))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112101))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112101))) h))

theorem cover_subtree_ecd8fe40a0e6 :
    adaptiveCoverCheck 7 thetaAboveCell000022112101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112101
    (by
      have h : ((childLL thetaAboveCell000022112101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112101) h)
    (by
      have h : ((childLH thetaAboveCell000022112101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112101) h)
    cover_subtree_4284ed2ee8d6
    cover_subtree_21c449726701

theorem cover_subtree_4e862092a132 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112102))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112102))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112102))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022112102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022112102)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022112102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022112102)) h)

theorem cover_subtree_aa7a39051514 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112102))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112102))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112102))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022112102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022112102)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022112102))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022112102))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022112102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022112102))) h))

theorem cover_subtree_bcfbc1ac2009 :
    adaptiveCoverCheck 7 thetaAboveCell000022112102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112102
    cover_subtree_4e862092a132
    cover_subtree_aa7a39051514
    (by
      have h : ((childHL thetaAboveCell000022112102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112102) h)
    (by
      have h : ((childHH thetaAboveCell000022112102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112102) h)

theorem cover_subtree_340b36315559 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112103))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112103))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022112103))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022112103))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022112103))) h))

theorem cover_subtree_3ea1443179e3 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112103))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112103))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022112103))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022112103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022112103))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022112103))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022112103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022112103))) h))

theorem cover_subtree_333ca6341b52 :
    adaptiveCoverCheck 7 thetaAboveCell000022112103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112103
    cover_subtree_340b36315559
    cover_subtree_3ea1443179e3
    (by
      have h : ((childHL thetaAboveCell000022112103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112103) h)
    (by
      have h : ((childHH thetaAboveCell000022112103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112103) h)

theorem cover_subtree_0a317c2968a3 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00002211)))
    cover_subtree_ff28352fdcbd
    cover_subtree_ecd8fe40a0e6
    cover_subtree_bcfbc1ac2009
    cover_subtree_333ca6341b52

theorem cover_subtree_0f6a5316da7f :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112110)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112110)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112110))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112110))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112110))) h))

theorem cover_subtree_8b21324e2245 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112110)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112110)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112110))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112110))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112110))) h))

theorem cover_subtree_2b3d980fd10a :
    adaptiveCoverCheck 7 thetaAboveCell000022112110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112110
    (by
      have h : ((childLL thetaAboveCell000022112110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112110) h)
    (by
      have h : ((childLH thetaAboveCell000022112110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112110) h)
    cover_subtree_0f6a5316da7f
    cover_subtree_8b21324e2245

theorem cover_subtree_3d8086490270 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022112111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022112111)
    (by
      have h : ((childLL (childHL thetaAboveCell000022112111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022112111)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022112111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022112111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022112111))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022112111))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022112111))) h))

theorem cover_subtree_13b36b31ee50 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022112111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022112111)
    (by
      have h : ((childLL (childHH thetaAboveCell000022112111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022112111)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022112111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022112111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022112111))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022112111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022112111))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022112111))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022112111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022112111))) h))

theorem cover_subtree_fe061292783d :
    adaptiveCoverCheck 7 thetaAboveCell000022112111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112111
    (by
      have h : ((childLL thetaAboveCell000022112111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022112111) h)
    (by
      have h : ((childLH thetaAboveCell000022112111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022112111) h)
    cover_subtree_3d8086490270
    cover_subtree_13b36b31ee50

theorem cover_subtree_acdbdc38c196 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112112))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112112))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022112112))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022112112))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022112112))) h))

theorem cover_subtree_f4b1386a9f86 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112112))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112112))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022112112))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022112112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022112112))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022112112))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022112112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022112112))) h))

theorem cover_subtree_280eb01136d6 :
    adaptiveCoverCheck 7 thetaAboveCell000022112112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112112
    cover_subtree_acdbdc38c196
    cover_subtree_f4b1386a9f86
    (by
      have h : ((childHL thetaAboveCell000022112112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112112) h)
    (by
      have h : ((childHH thetaAboveCell000022112112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112112) h)

theorem cover_subtree_3add30d6277d :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022112113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022112113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022112113))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022112113))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022112113))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022112113))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022112113))) h))

theorem cover_subtree_4b342ee841c3 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022112113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022112113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022112113))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022112113))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022112113))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022112113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022112113))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022112113))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022112113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022112113))) h))

theorem cover_subtree_95d32084082d :
    adaptiveCoverCheck 7 thetaAboveCell000022112113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022112113
    cover_subtree_3add30d6277d
    cover_subtree_4b342ee841c3
    (by
      have h : ((childHL thetaAboveCell000022112113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022112113) h)
    (by
      have h : ((childHH thetaAboveCell000022112113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022112113) h)

theorem cover_subtree_9112d0843a89 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00002211)))
    cover_subtree_2b3d980fd10a
    cover_subtree_fe061292783d
    cover_subtree_280eb01136d6
    cover_subtree_95d32084082d

theorem e24KC2ThetaAboveLeaf0000221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00002211))
    cover_subtree_0a317c2968a3
    cover_subtree_9112d0843a89
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112120 h)
        (by
          have h : (thetaAboveCell000022112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112121 h)
        (by
          have h : (thetaAboveCell000022112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112122 h)
        (by
          have h : (thetaAboveCell000022112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112130 h)
        (by
          have h : (thetaAboveCell000022112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112131 h)
        (by
          have h : (thetaAboveCell000022112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112132 h)
        (by
          have h : (thetaAboveCell000022112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022112133 h))
theorem e24KC2ThetaAboveLeaf0000221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00002211))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00002211))) h)
theorem e24KC2ThetaAboveLeaf0000221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00002211))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00002211))) h)
theorem cover_subtree_c69725c188d3 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113000)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113000)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113000))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113000))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113000))) h))

theorem cover_subtree_a8d579475d23 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113000)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113000)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113000))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113000)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113000))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113000))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113000))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113000))) h))

theorem cover_subtree_560b815bd286 :
    adaptiveCoverCheck 7 thetaAboveCell000022113000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113000
    (by
      have h : ((childLL thetaAboveCell000022113000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113000) h)
    (by
      have h : ((childLH thetaAboveCell000022113000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113000) h)
    cover_subtree_c69725c188d3
    cover_subtree_a8d579475d23

theorem cover_subtree_995ab0851a0f :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113001)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113001)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113001))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113001))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113001))) h))

theorem cover_subtree_f5e3b9ffae68 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113001)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113001)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113001))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113001)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113001))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113001))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113001))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113001))) h))

theorem cover_subtree_e2b5567129eb :
    adaptiveCoverCheck 7 thetaAboveCell000022113001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113001
    (by
      have h : ((childLL thetaAboveCell000022113001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113001) h)
    (by
      have h : ((childLH thetaAboveCell000022113001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113001) h)
    cover_subtree_995ab0851a0f
    cover_subtree_f5e3b9ffae68

theorem cover_subtree_2a8071ef107e :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113002))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113002))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022113002))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022113002))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022113002))) h))

theorem cover_subtree_1f4e667d89aa :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113002))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113002))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLH thetaAboveCell000022113002))
        (by
          have h : ((childLL (childHL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childHL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childHL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childHL (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLH
            thetaAboveCell000022113002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLH thetaAboveCell000022113002))
        (by
          have h : ((childLL (childHH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childLH (childHH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHL (childHH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLH
            thetaAboveCell000022113002))) h)
        (by
          have h : ((childHH (childHH (childLH thetaAboveCell000022113002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLH
            thetaAboveCell000022113002))) h))

theorem cover_subtree_cf43677b186a :
    adaptiveCoverCheck 7 thetaAboveCell000022113002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113002
    cover_subtree_2a8071ef107e
    cover_subtree_1f4e667d89aa
    (by
      have h : ((childHL thetaAboveCell000022113002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022113002) h)
    (by
      have h : ((childHH thetaAboveCell000022113002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022113002) h)

theorem cover_subtree_e06c4b38ee49 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113003))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113003))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childLL thetaAboveCell000022113003))
        (by
          have h : ((childLL (childHL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childHL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childHL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childHL (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childLL
            thetaAboveCell000022113003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childLL thetaAboveCell000022113003))
        (by
          have h : ((childLL (childHH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childHH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childHH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childLL
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childHH (childLL thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childLL
            thetaAboveCell000022113003))) h))

theorem cover_subtree_5735fc3146a5 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113003))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113003))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113003))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113003))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022113003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022113003)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022113003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022113003)) h)

theorem cover_subtree_b9715c0ddc62 :
    adaptiveCoverCheck 7 thetaAboveCell000022113003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113003
    cover_subtree_e06c4b38ee49
    cover_subtree_5735fc3146a5
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113003)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113003)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113003)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113003)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113003))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113003)) h))

theorem cover_subtree_0338ef548092 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00002211)))
    cover_subtree_560b815bd286
    cover_subtree_e2b5567129eb
    cover_subtree_cf43677b186a
    cover_subtree_b9715c0ddc62

theorem cover_subtree_8babef05283e :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113010)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113010)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113010))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113010))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113010))) h))

theorem cover_subtree_453a26c2a0ce :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113010)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113010)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113010))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113010)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113010))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113010))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113010))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113010))) h))

theorem cover_subtree_9a8d1e8ff5df :
    adaptiveCoverCheck 7 thetaAboveCell000022113010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113010
    (by
      have h : ((childLL thetaAboveCell000022113010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113010) h)
    (by
      have h : ((childLH thetaAboveCell000022113010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113010) h)
    cover_subtree_8babef05283e
    cover_subtree_453a26c2a0ce

theorem cover_subtree_d4f84dde625a :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113011)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113011)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113011))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113011))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113011))) h))

theorem cover_subtree_a97cdaa163bd :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113011)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113011)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113011))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113011)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113011))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113011))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113011))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113011))) h))

theorem cover_subtree_caad7b9ebe18 :
    adaptiveCoverCheck 7 thetaAboveCell000022113011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113011
    (by
      have h : ((childLL thetaAboveCell000022113011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113011) h)
    (by
      have h : ((childLH thetaAboveCell000022113011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113011) h)
    cover_subtree_d4f84dde625a
    cover_subtree_a97cdaa163bd

theorem cover_subtree_fbb8d3b85bf4 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113012))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113012))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113012))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022113012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022113012)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022113012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022113012)) h)

theorem cover_subtree_f025663eb4cc :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113012))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113012))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113012))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113012))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022113012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022113012)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022113012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022113012)) h)

theorem cover_subtree_6d9b8f942e07 :
    adaptiveCoverCheck 7 thetaAboveCell000022113012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113012
    cover_subtree_fbb8d3b85bf4
    cover_subtree_f025663eb4cc
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113012)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113012)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113012)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113012)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113012))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113012)) h))

theorem cover_subtree_c85e1b57b2c5 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113013))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113013))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113013))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022113013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022113013)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022113013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022113013)) h)

theorem cover_subtree_a12be2bf4817 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113013))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113013))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113013))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113013))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022113013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022113013)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022113013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022113013)) h)

theorem cover_subtree_d1382a844a10 :
    adaptiveCoverCheck 7 thetaAboveCell000022113013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113013
    cover_subtree_c85e1b57b2c5
    cover_subtree_a12be2bf4817
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113013)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113013)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113013)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113013)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113013))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113013)) h))

theorem cover_subtree_d4d29d86cd96 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00002211)))
    cover_subtree_9a8d1e8ff5df
    cover_subtree_caad7b9ebe18
    cover_subtree_6d9b8f942e07
    cover_subtree_d1382a844a10

theorem e24KC2ThetaAboveLeaf0000221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00002211))
    cover_subtree_0338ef548092
    cover_subtree_d4d29d86cd96
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113020 h)
        (by
          have h : (thetaAboveCell000022113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113021 h)
        (by
          have h : (thetaAboveCell000022113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113022 h)
        (by
          have h : (thetaAboveCell000022113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113030 h)
        (by
          have h : (thetaAboveCell000022113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113031 h)
        (by
          have h : (thetaAboveCell000022113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113032 h)
        (by
          have h : (thetaAboveCell000022113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113033 h))
theorem cover_subtree_836d962e65ac :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113100)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113100)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113100))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113100))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113100))) h))

theorem cover_subtree_ecf6c7f90571 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113100)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113100)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113100))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113100)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113100))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113100))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113100))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113100))) h))

theorem cover_subtree_fa2b1e57d306 :
    adaptiveCoverCheck 7 thetaAboveCell000022113100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113100
    (by
      have h : ((childLL thetaAboveCell000022113100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113100) h)
    (by
      have h : ((childLH thetaAboveCell000022113100)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113100) h)
    cover_subtree_836d962e65ac
    cover_subtree_ecf6c7f90571

theorem cover_subtree_2c032bc482bc :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113101)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113101)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113101))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113101))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113101))) h))

theorem cover_subtree_3eddb0efc253 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113101)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113101)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113101))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113101)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113101))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113101))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113101))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113101))) h))

theorem cover_subtree_cbdd15c92455 :
    adaptiveCoverCheck 7 thetaAboveCell000022113101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113101
    (by
      have h : ((childLL thetaAboveCell000022113101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113101) h)
    (by
      have h : ((childLH thetaAboveCell000022113101)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113101) h)
    cover_subtree_2c032bc482bc
    cover_subtree_3eddb0efc253

theorem cover_subtree_e867c54455aa :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022113102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022113102))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022113102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022113102))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022113102))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022113102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022113102)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022113102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022113102)) h)

theorem cover_subtree_d8e5977bc823 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022113102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022113102))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022113102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022113102))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022113102))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022113102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022113102))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022113102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022113102)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022113102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022113102)) h)

theorem cover_subtree_81e578425a2e :
    adaptiveCoverCheck 7 thetaAboveCell000022113102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113102
    cover_subtree_e867c54455aa
    cover_subtree_d8e5977bc823
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113102)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113102)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113102)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113102)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113102))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113102)) h))

theorem cover_subtree_6af7504512c8 :
    adaptiveCoverCheck 7 thetaAboveCell000022113103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113103
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113103)
        (by
          have h : ((childLL (childLL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022113103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113103)
        (by
          have h : ((childLL (childLH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022113103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113103)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113103)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113103)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113103)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113103))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113103)) h))

theorem cover_subtree_dc05a5cb4d61 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002211)))
    cover_subtree_fa2b1e57d306
    cover_subtree_cbdd15c92455
    cover_subtree_81e578425a2e
    cover_subtree_6af7504512c8

theorem cover_subtree_fcbdf3a9e595 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113110)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113110)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113110))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113110))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113110))) h))

theorem cover_subtree_2828e56e478f :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113110)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113110)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113110))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113110)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113110))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113110))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113110))) h))

theorem cover_subtree_15fb86545eea :
    adaptiveCoverCheck 7 thetaAboveCell000022113110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113110
    (by
      have h : ((childLL thetaAboveCell000022113110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113110) h)
    (by
      have h : ((childLH thetaAboveCell000022113110)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113110) h)
    cover_subtree_fcbdf3a9e595
    cover_subtree_2828e56e478f

theorem cover_subtree_0f38c8258b2e :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022113111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113111)
    (by
      have h : ((childLL (childHL thetaAboveCell000022113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL thetaAboveCell000022113111)) h)
    (by
      have h : ((childLH (childHL thetaAboveCell000022113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL thetaAboveCell000022113111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022113111))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022113111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022113111))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022113111))) h))

theorem cover_subtree_13fc46665967 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022113111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113111)
    (by
      have h : ((childLL (childHH thetaAboveCell000022113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH thetaAboveCell000022113111)) h)
    (by
      have h : ((childLH (childHH thetaAboveCell000022113111))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH thetaAboveCell000022113111)) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022113111))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022113111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022113111))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022113111))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022113111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022113111))) h))

theorem cover_subtree_83c447d13cd0 :
    adaptiveCoverCheck 7 thetaAboveCell000022113111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113111
    (by
      have h : ((childLL thetaAboveCell000022113111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022113111) h)
    (by
      have h : ((childLH thetaAboveCell000022113111)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022113111) h)
    cover_subtree_0f38c8258b2e
    cover_subtree_13fc46665967

theorem cover_subtree_02c32f65c578 :
    adaptiveCoverCheck 7 thetaAboveCell000022113112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113112
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113112)
        (by
          have h : ((childLL (childLL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113112)
        (by
          have h : ((childLL (childLH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113112)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113112)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113112)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113112)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113112))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113112)) h))

theorem cover_subtree_74079318656f :
    adaptiveCoverCheck 7 thetaAboveCell000022113113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022113113
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022113113)
        (by
          have h : ((childLL (childLL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022113113)
        (by
          have h : ((childLL (childLH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022113113)
        (by
          have h : ((childLL (childHL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childLH (childHL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHL (childHL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHL
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHH (childHL thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHL
            thetaAboveCell000022113113)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022113113)
        (by
          have h : ((childLL (childHH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childHH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childLH (childHH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childHH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHL (childHH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childHH
            thetaAboveCell000022113113)) h)
        (by
          have h : ((childHH (childHH thetaAboveCell000022113113))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childHH
            thetaAboveCell000022113113)) h))

theorem cover_subtree_6a41f1f44284 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002211))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002211)))
    cover_subtree_15fb86545eea
    cover_subtree_83c447d13cd0
    cover_subtree_02c32f65c578
    cover_subtree_74079318656f

theorem e24KC2ThetaAboveLeaf0000221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002211))
    cover_subtree_dc05a5cb4d61
    cover_subtree_6a41f1f44284
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113120 h)
        (by
          have h : (thetaAboveCell000022113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113121 h)
        (by
          have h : (thetaAboveCell000022113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113122 h)
        (by
          have h : (thetaAboveCell000022113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00002211)))
        (by
          have h : (thetaAboveCell000022113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113130 h)
        (by
          have h : (thetaAboveCell000022113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113131 h)
        (by
          have h : (thetaAboveCell000022113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113132 h)
        (by
          have h : (thetaAboveCell000022113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022113133 h))
theorem e24KC2ThetaAboveLeaf0000221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002211))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002211))) h)
theorem e24KC2ThetaAboveLeaf0000221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002211))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002211))) h)
theorem e24KC2ThetaAboveLeaf0000230002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00002300))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00002300))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00002300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023000220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000220 h)
        (by
          have h : (thetaAboveCell000023000221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000221 h)
        (by
          have h : (thetaAboveCell000023000222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000222 h)
        (by
          have h : (thetaAboveCell000023000223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023000230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000230 h)
        (by
          have h : (thetaAboveCell000023000231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000231 h)
        (by
          have h : (thetaAboveCell000023000232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000232 h)
        (by
          have h : (thetaAboveCell000023000233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000233 h))
theorem e24KC2ThetaAboveLeaf0000230003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00002300))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00002300))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00002300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023000320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000320 h)
        (by
          have h : (thetaAboveCell000023000321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000321 h)
        (by
          have h : (thetaAboveCell000023000322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000322 h)
        (by
          have h : (thetaAboveCell000023000323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023000330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000330 h)
        (by
          have h : (thetaAboveCell000023000331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000331 h)
        (by
          have h : (thetaAboveCell000023000332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000332 h)
        (by
          have h : (thetaAboveCell000023000333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023000333 h))
theorem e24KC2ThetaAboveLeaf0000230012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00002300))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00002300))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00002300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023001220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001220 h)
        (by
          have h : (thetaAboveCell000023001221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001221 h)
        (by
          have h : (thetaAboveCell000023001222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001222 h)
        (by
          have h : (thetaAboveCell000023001223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLH
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023001230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001230 h)
        (by
          have h : (thetaAboveCell000023001231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001231 h)
        (by
          have h : (thetaAboveCell000023001232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001232 h)
        (by
          have h : (thetaAboveCell000023001233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001233 h))
theorem e24KC2ThetaAboveLeaf0000230013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00002300))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00002300))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00002300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00002300))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLH
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023001320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001320 h)
        (by
          have h : (thetaAboveCell000023001321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001321 h)
        (by
          have h : (thetaAboveCell000023001322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001322 h)
        (by
          have h : (thetaAboveCell000023001323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLH
        thetaAboveCell00002300)))
        (by
          have h : (thetaAboveCell000023001330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001330 h)
        (by
          have h : (thetaAboveCell000023001331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001331 h)
        (by
          have h : (thetaAboveCell000023001332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001332 h)
        (by
          have h : (thetaAboveCell000023001333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000023001333 h))

end PartE
end GerverSofa

end

end

end

end

end

end
