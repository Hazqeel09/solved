import Research.ICGGeneralBridge

/-! Probe: the reused bridge (H. Dong, ai4math-results, Apache-2.0) applies to even orders
`2^a * p^b`, since it only assumes that the two primes are distinct. -/

open ICGBridge ICGGeneral in
example (a b p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (D : Finset ℕ) :
    energy (icgAdj (2 ^ a * p ^ b) D) (icgAdj_isHermitian _ _) =
      L1mat 2 p a b (fun c e => if 2 ^ c * p ^ e ∈ D then 1 else 0) := by
  simpa using energy_icgAdj_pq 2 p a b Nat.prime_two hp (Ne.symm hp2) D
