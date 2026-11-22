module

public import GRHCorollaries.Mills.Main
public import GRHCorollaries.Cubes.Main

/-!
Axiom audit of the headline theorems. Run `scripts/axioms.sh`; every line must list only
`propext`, `Classical.choice`, `Quot.sound`.
-/

@[expose] public section

#print axioms Mills.lower_bound_of_RH
#print axioms Mills.exists_isMinMills_of_RH
#print axioms Mills.exists_isMills_of_RH
#print axioms GRHCorollaries.exists_prime_between_cubes_of_RH
#print axioms GRHCorollaries.exists_prime_between_consecutive_cubes_of_RH
#print axioms GRHCorollaries.Cubes.exists_prime_between_cubes_of_le
#print axioms GRHCorollaries.abs_psi_sub_self_le_of_RH
