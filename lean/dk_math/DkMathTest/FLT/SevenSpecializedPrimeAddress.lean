import DkMath.FLT.Seven

open DkMath.FLT.Seven

/-- Permanent regression guard: generic routing permits repeated diagonal
prime support, so address uniqueness must stay specialized to FLT7 packets. -/
def genericAddressCounterexample : CoprimeTripleRouting 2 2 1 2 2 1 where
  c11 := 2
  c12 := 1
  c13 := 1
  c21 := 1
  c22 := 2
  c23 := 1
  c31 := 1
  c32 := 1
  c33 := 1
  row1 := by norm_num
  row2 := by norm_num
  row3 := by norm_num
  col1 := by norm_num
  col2 := by norm_num
  col3 := by norm_num
  row1_coprime := by norm_num
  row2_coprime := by norm_num
  row3_coprime := by norm_num
  col1_coprime := by norm_num
  col2_coprime := by norm_num
  col3_coprime := by norm_num

example : 2 ∣ routingCell genericAddressCounterexample .y .sevenV := by
  norm_num [routingCell, genericAddressCounterexample]

example : 2 ∣ routingCell genericAddressCounterexample .z .leftCubic := by
  norm_num [routingCell, genericAddressCounterexample]

example {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow} {column₁ column₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r.routing row₁ column₁)
    (h₂ : q ∣ routingCell r.routing row₂ column₂) : row₁ = row₂ :=
  r.row_eq_of_prime_dvd_cells hq h₁ h₂

example {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow} {column₁ column₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r.routing row₁ column₁)
    (h₂ : q ∣ routingCell r.routing row₂ column₂) : column₁ = column₂ :=
  r.column_eq_of_prime_dvd_cells hq h₁ h₂

example {x y z q : ℕ} (r : AwayCubicRoutingPacket x y z) (hq : Nat.Prime q)
    {row₁ row₂ : EndpointRoutingRow} {column₁ column₂ : RootRoutingColumn}
    (h₁ : q ∣ routingCell r.routing row₁ column₁)
    (h₂ : q ∣ routingCell r.routing row₂ column₂) :
    row₁ = row₂ ∧ column₁ = column₂ :=
  r.prime_address_unique hq h₁ h₂

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (a : AwayRoutingPrimeAddress r) :
    padicValNat a.q (routingCell r.routing a.row a.column) =
      padicValNat a.q (endpointRoutingFactorNat y z a.row) :=
  a.cell_depth_eq_endpoint_depth

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (a : AwayRoutingPrimeAddress r) :
    padicValNat a.q (routingCell r.routing a.row a.column) =
      padicValNat a.q (rootRoutingFactorNat r a.column) :=
  a.cell_depth_eq_root_depth

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (a : AwayRoutingPrimeAddress r) : AwayRoutingPrimeDepthPacket r :=
  a.toDepthPacket

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (a : AwayRoutingPrimeAddress r) {column' : RootRoutingColumn}
    (h : column' ≠ a.column) :
    ¬ a.q ∣ routingCell r.routing a.row column' :=
  a.not_dvd_other_column h

example {x y z : ℕ} {r : AwayCubicRoutingPacket x y z}
    (a : AwayRoutingPrimeAddress r) {row' : EndpointRoutingRow}
    (h : row' ≠ a.row) :
    ¬ a.q ∣ routingCell r.routing row' a.column :=
  a.not_dvd_other_row h

#print axioms AwayCubicRoutingPacket.prime_address_unique
#print axioms AwayRoutingPrimeAddress.cell_depth_eq_endpoint_depth
#print axioms AwayRoutingPrimeAddress.cell_depth_eq_root_depth
#print axioms AwayRoutingPrimeAddress.toDepthPacket
