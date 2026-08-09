import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

/-- The finite product of finsets, represented as a finset of functions. -/
def piFinset {d : ℕ} (s : Fin d → Finset ℤ) : Finset (Fin d → ℤ) :=
  Finset.univ.filter (fun n => ∀ a, n a ∈ s a)

/--
  For each integer m, we define the set

      { n ∈ ℤᵈ | max(n₁, ..., n_d) ≤ N }
-/
def S' (N : ℕ) (d : ℕ) : Finset (Fin d → ℤ) :=
  piFinset (fun _ => Finset.Ico (-(N : ℤ)) ((N : ℤ) + 1))

/--
  For each integer m, we define the set

      { n ∈ ℤᵈ | max(|n₁|, ..., |n_d|) = N}
-/
def S (N : ℕ) (d : ℕ) : Finset (Fin d → ℤ) :=
  Finset.filter (fun n => ∃ i : Fin d, (n i).natAbs = N) (S' N d)

/-- The part of `S N d` on which the `i`-th coordinate is extremal. -/
def S_aux (N : ℕ) (d : ℕ) (i : Fin d) : Finset (Fin d → ℤ) :=
  piFinset (fun a => if a = i then {- (N : ℤ), (N : ℤ)}
    else Finset.Ico (-(N : ℤ)) ((N : ℤ) + 1))

lemma S_is_union (N : ℕ) (d : ℕ) :
    S N d = (Finset.univ : Finset (Fin d)).biUnion (fun i => S_aux N d i) := by
  classical
  ext n
  simp [S, S', S_aux, piFinset]

lemma S_aux_card (N : ℕ) (d : ℕ) (i : Fin d) :
    (S_aux N d i).card ≤ 2 * (2 * N + 1) ^ (d - 1) := by
  -- Original Lean 3 `sorry` (line 118), retained as an explicit port gap.
  sorry

lemma S_card_le (N : ℕ) (d : ℕ) :
    (S N d).card ≤ 2 * d * (2 * N + 1) ^ (d - 1) := by
  calc
    (S N d).card = ((Finset.univ : Finset (Fin d)).biUnion (fun i => S_aux N d i)).card := by
      rw [S_is_union]
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin d)), (S_aux N d i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ i : Fin d, 2 * (2 * N + 1) ^ (d - 1) := by
      -- Original Lean 3 `sorry` (line 185), for `sum_le_sum`, retained explicitly.
      sorry
    _ = 2 * d * (2 * N + 1) ^ (d - 1) := by
      simp [Finset.sum_const_nat]
