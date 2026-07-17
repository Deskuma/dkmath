/-
Copyright (c) 2026 D. and Wise Wolf. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: D. and Wise Wolf.
-/

import DkMath.Collatz.PetalBridge.UpperWindow
import DkMath.Collatz.PetalBridge.FloatWindow.WidthBalance
import DkMath.Collatz.PetalBridge.FloatWindow.DyadicFloat
import DkMath.Collatz.PetalBridge.FloatWindow.OrbitBalance
import DkMath.Collatz.PetalBridge.FloatWindow.PatternLedger
import DkMath.Collatz.PetalBridge.FloatWindow.DriftBridge
import DkMath.Collatz.PetalBridge.FloatWindow.PressureIncidenceBridge
import DkMath.Collatz.PetalBridge.FloatWindow.PaymentMultiplicityBridge
import DkMath.Collatz.PetalBridge.FloatWindow.PaymentBlockBridge
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlock
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentFamily
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPressure
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentRepayment
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentDepthLedger
import DkMath.Collatz.PetalBridge.FloatWindow.FiniteReflectedQueue
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentScalarQueue
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentBlockNormalForm
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPositiveBlock
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentPrimitiveExcursion
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSaturatedSuccessor
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentSelectedCarrier
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmplitude
import DkMath.Collatz.PetalBridge.FloatWindow.FiniteAmortizedResource
import DkMath.Collatz.PetalBridge.FloatWindow.UniversalPaymentAmortizedResource
import DkMath.Collatz.PetalBridge.FloatWindow.BoundedRepaymentLag
import DkMath.Collatz.PetalBridge.FloatWindow.FiniteSignedTransition
import DkMath.Collatz.PetalBridge.FloatWindow.FinitePotentialIncompleteness
import DkMath.Collatz.PetalBridge.FloatWindow.FiniteControlCounter
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceTimeLag
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueue
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalOwnedQueueGlobal
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFlow
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeHorizon
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalSourceAgeFiniteCertificate
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointDrift
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalEndpointConservation
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalHighDrift
import DkMath.Collatz.PetalBridge.FloatWindow.CanonicalAllOnesDrift
import DkMath.Collatz.PetalBridge.FloatWindow.RawLowSignatureObstruction

#print "file: DkMath.Collatz.PetalBridge.FloatWindow"

/-!
# Exact dyadic Float window

Public entry point for the upper/lower binary observation of `3*n+1`.
All arithmetic below this module is exact natural-number arithmetic.
-/
