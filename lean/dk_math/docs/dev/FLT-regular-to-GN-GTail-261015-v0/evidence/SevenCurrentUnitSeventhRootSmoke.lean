import DkMath

open DkMath.FLT.Seven.SevenRealCubicInt DkMath.FLT.Kummer.SevenRealGN

#check rotation_fixed_mod_seven_integer
#check current_rho_congruent_integer
#check current_primary_packet_unit_seventh
#check currentCarrier_unit_free_factor_receiver
#check current_unit_free_root_not_real

-- The two existing theorem statements are unchanged by the balanced expansion.
#print axioms thetaLinear_pow_seven
#print axioms thetaSquare_pow_seven

run_cmd do
  for n in #[``DkMath.FLT.Seven.SevenRealCubicInt.thetaLinear_pow_seven,
      ``DkMath.FLT.Seven.SevenRealCubicInt.thetaSquare_pow_seven] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in balanced coordinate proof {n}"
  Lean.logInfo "PASS: two existing coordinate proofs; standard axiom whitelist only."
