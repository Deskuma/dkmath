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

#print "file: DkMath.Collatz.PetalBridge.FloatWindow"

/-!
# Exact dyadic Float window

Public entry point for the upper/lower binary observation of `3*n+1`.
All arithmetic below this module is exact natural-number arithmetic.
-/
