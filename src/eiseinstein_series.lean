import algebra.module.basic
import data.real.basic
import data.complex.basic
import algebra.module.submodule
import linear_algebra.finite_dimensional


namespace submodule

/-- Let V be a finite dimensional real vector space-/
variables {V: Type} [add_comm_group V][vector_space ℝ V][finite_dimensional ℝ V]

--variables {dim: Type} [decidable_eq dim][fintype dim] 
/--

# Lattices (incomplete)
A Lattice Γ ≤ V is a discrete subgroup under addtion of finite rank, whick generates V as an ℝ subspace. 
--/
class Lattice (Γ: add_subgroup V) --{n : Type*} [decidable_eq n] [fintype n] : Type := -- [add_subgroup V Γ] [add_comm_group Γ] [semimodule ℂ Γ] :=
 --sorry

--variables (Γ: add_subgroup V)[Lattice Γ]

/--
# Eiseinstein series of weight k (incomplete)
The Eiseinstein series of weight k is a function sending a Lattice to ...
-/
def G (k: ℕ)(Γ: add_subgroup V)[Lattice Γ] : ℂ:= 
sorry



end submodule
