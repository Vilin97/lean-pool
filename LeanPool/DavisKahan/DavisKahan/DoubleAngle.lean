/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

import LeanPool.DavisKahan.DavisKahan.DoubleAngle.All
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.AngleTransport
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.CompatibilitySinTwoTheta
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.DirectedAngleGeneric
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.DirectedAngleRealTransport
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.KyFanOrthonormal
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealAngleIdentification
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealUnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.ReflectionTangentKyFan
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.ScalarDoubleAngleTangent
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.ScalarTransport
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaApproximatePair
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaBranchFree
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaKyFan
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaKyFanFiniteCarrier
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TangentTransport
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.Unbounded
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.UnboundedIdealFormGap

/-! Supporting modules for Davis–Kahan rotation of eigenvectors. -/
