import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq

open Matrix
open scoped MatrixGroups

lemma det_2x2 (M : Matrix (Fin 2) (Fin 2) ℤ) :
    M.det = M 0 0 * M 1 1 - M 1 0 * M 0 1 := by
  rw [Matrix.det_fin_two]
  ring

namespace Matrix.SpecialLinearGroup

variable {M : SL(2, ℤ)}

lemma inverse₀₀ : M⁻¹ 0 0 = M 1 1 := by
  rw [SL2_inv_expl]
  rfl

lemma inverse₀₁ : M⁻¹ 0 1 = -M 0 1 := by
  rw [SL2_inv_expl]
  rfl

lemma inverse₁₀ : M⁻¹ 1 0 = -M 1 0 := by
  rw [SL2_inv_expl]
  rfl

section CongruenceSubgroups

variable {N : ℕ} [Fact (0 < N)]

structure mem_principal_subgroup (M : SL(2, ℤ)) : Prop where
  cond₀₀ : M 0 0 ≡ 1 [ZMOD N]
  cond₀₁ : M 0 1 ≡ 0 [ZMOD N]
  cond₁₀ : M 1 0 ≡ 0 [ZMOD N]

lemma principal_condition₁₁ (M : SL(2, ℤ)) :
    mem_principal_subgroup (N := N) M → M 1 1 ≡ 1 [ZMOD N] := by
  rintro ⟨h00, h01, h10⟩
  have hdet : M 0 0 * M 1 1 - M 1 0 * M 0 1 = 1 := by
    rw [← det_2x2 (M : Matrix (Fin 2) (Fin 2) ℤ)]
    exact M.prop
  have hdet_mod : M 0 0 * M 1 1 - M 1 0 * M 0 1 ≡ 1 [ZMOD N] := by
    rw [hdet]
  have h00mul : M 0 0 * M 1 1 ≡ 1 * M 1 1 [ZMOD N] :=
    h00.mul (Int.ModEq.refl _)
  have h10mul : M 1 0 * M 0 1 ≡ 0 * 0 [ZMOD N] :=
    h10.mul h01
  have hsub : M 0 0 * M 1 1 - M 1 0 * M 0 1 ≡ M 1 1 [ZMOD N] := by
    simpa using h00mul.sub h10mul
  exact hsub.symm.trans hdet_mod

/--
The principal congruence subgroup of level `N` (with `N > 0`) is
`Γ(N) = {γ ∈ SL(2, ℤ) | γ ≡ id (mod N)}`.
-/
def principal_congurence_subgroup : Subgroup (SL(2, ℤ)) where
  carrier := {M | mem_principal_subgroup (N := N) M}
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩ <;> simp
  mul_mem' := by
    rintro A B ⟨hA00, hA01, hA10⟩ ⟨hB00, hB01, hB10⟩
    have hmul := Matrix.two_mul_expl (A : Matrix (Fin 2) (Fin 2) ℤ)
      (B : Matrix (Fin 2) (Fin 2) ℤ)
    refine ⟨?_, ?_, ?_⟩
    · rw [SpecialLinearGroup.coe_mul, hmul.1]
      simpa using (hA00.mul hB00).add (hA01.mul hB10)
    · rw [SpecialLinearGroup.coe_mul, hmul.2.1]
      simpa using (hA00.mul hB01).add (hA01.mul (Int.ModEq.refl _))
    · rw [SpecialLinearGroup.coe_mul, hmul.2.2.1]
      simpa using (hA10.mul hB00).add ((Int.ModEq.refl _).mul hB10)
  inv_mem' := by
    rintro A ⟨hA00, hA01, hA10⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [inverse₀₀]
      exact principal_condition₁₁ (N := N) A ⟨hA00, hA01, hA10⟩
    · rw [inverse₀₁]
      simpa using hA01.neg
    · rw [inverse₁₀]
      simpa using hA10.neg

end CongruenceSubgroups

end Matrix.SpecialLinearGroup
