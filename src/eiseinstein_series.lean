import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic


namespace Submodule

/- Let V be a finite dimensional real vector space -/
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

--variables {dim : Type*} [DecidableEq dim] [Fintype dim]
/--

# Lattices (incomplete)
A Lattice Γ ≤ V is a discrete subgroup under addition of finite rank, which generates V as an ℝ subspace.
-/
class Lattice (Γ : AddSubgroup V)
 --sorry

--variables (Γ : AddSubgroup V) [Lattice Γ]

/--
# Eiseinstein series of weight k (incomplete)
The Eiseinstein series of weight k is a function sending a Lattice to ...
-/
def G (k : ℕ) (Γ : AddSubgroup V) [Lattice Γ] : ℂ :=
  sorry



end Submodule
