
import linear_algebra.special_linear_group
import data.zmod.basic

open matrix

lemma det_2x2 (M : matrix (fin 2) (fin 2) ℤ) : M.det = M 0 0 * M 1 1 - M 1 0 * M 0 1 :=
calc M.det = ((1 : units ℤ) * (_ * (_ * 1))) + (((-1 : units ℤ) * (_ * (_ * 1))) + 0) : refl M.det
... = M 0 0 * M 1 1 - M 1 0 * M 0 1 : by { simp, ring }

local notation `SL₂`(R) := special_linear_group (fin 2) R

section basic_matrix_lemmas

    variable M: SL₂(ℤ)

    lemma inverse₀₀ : M⁻¹ 0 0 = M 1 1 :=
    show (1*(1* ( _ * 1)): ℤ) + ( -1 *( _ * 0) + 0) = _ , by {simp, ring}

    lemma inverse₀₁ : M⁻¹ 0 1 = - M 0 1 :=
    show (1 * (_ * 0): ℤ) + (-1 * (1* (_ * 1)) + 0) = _, by {simp, ring}

    lemma inverse₁₀ : M⁻¹ 1 0 = - M 1 0 :=
    show (1 * (0 * (_ * 1)) : ℤ) + (-1 * (_ * _) + 0) = _, by {simp, ring}

end basic_matrix_lemmas

section congruence_subgroups
parameters {N : ℕ}[fact (0 < N)]
namespace special_linear_group

    structure mem_principal_subgroup (M: SL₂(ℤ)): Prop :=
    ( cond₀₀ : M 0 0  ≡ 1 [ZMOD N])
    ( cond₀₁ : M 0 1  ≡ 0 [ZMOD N])
    ( cond₁₀ : M 1 0  ≡ 0 [ZMOD N])

    lemma principal_condition₁₁ (M : SL₂ (ℤ)) : mem_principal_subgroup M  → M 1 1 ≡ 1 [ZMOD N]:=
            begin
                rintro ⟨M₁, M₂, M₃⟩,
                cases M,
                rw det_2x2 at M_property,
                have M_prop_mod_N : M_val 0 0 * M_val 1 1 - M_val 1 0 * M_val 0 1 ≡ 1 [ZMOD N]:=
                begin
                    tauto,
                end,
                have P₁: M_val 1 0 * M_val 0 1 ≡ 0 * 0 [ZMOD N],
                    apply int.modeq.modeq_mul;
                    assumption,
                have P₂: M_val 0 0 * M_val 1 1 ≡ 1 * M_val 1 1 [ZMOD N],
                    apply int.modeq.modeq_mul,
                    assumption,
                    refl,
                have P₃ : M_val 0 0 * M_val 1 1 - M_val 1 0 * M_val 0 1 ≡ M_val 0 0 * M_val 1 1 - 0 [ZMOD ↑N],
                    apply int.modeq.modeq_sub,
                    refl,
                    convert P₁,
                apply int.modeq.trans,
                rotate,
                exact M_prop_mod_N,
                simp at P₂,
                simp at P₃,
                apply int.modeq.trans,
                exact P₂.symm,
                apply int.modeq.trans,
                exact P₃.symm,
                refl,
            end

open int.modeq 
    /--
        The principal congruence subgroup of level N (N>1) is
                        Γ(N)={γ ∈ SL₂(ℤ) | γ ≅ id (mod N)}    
    -/
    definition principal_congurence_subgroup: subgroup SL₂(ℤ) :=
    {
        carrier := λ M , mem_principal_subgroup M,
        one_mem' := 
           rfl.mpr ⟨int.modeq.refl _, int.modeq.refl _, int.modeq.refl _⟩,
        mul_mem' := 
            begin
                rintros A B ⟨ A₀₀, A₀₁, A₁₀⟩ ⟨ B₀₀, B₀₁ , B₁₀ ⟩,

                have h : mem_principal_subgroup (A*B) :=
                begin
                    split,
                    {
                        show (A 0 0 * B 0 0) + (A 0 1 * B 1 0 + 0) ≡ 1 [ZMOD N],
                        ring,
                        rw (show (1 : ℤ) = 1 * 1 + 0 * 0, by ring),
                        apply int.modeq.modeq_add;
                        apply int.modeq.modeq_mul;
                        try {assumption};
                        refl,
                    },
                    {
                       show (A 0 0 * B 0 1) + (A 0 1 * B 1 1 + 0) ≡ 0 [ZMOD N],
                       ring, 
                       rw (show (0 : ℤ) = A 0 0 * 0 + 0 * B 1 1, by ring),
                        apply int.modeq.modeq_add;
                        apply int.modeq.modeq_mul;
                        try {assumption};
                        refl,
                    },
                    
                     show (A 1 0 * B 0 0) + (A 1 1 * B 1 0 + 0) ≡ 0 [ZMOD N],
                        ring,
                        rw (show (0 : ℤ) = 0 * B 0 0 + A 1 1 * 0, by ring),
                        apply int.modeq.modeq_add;
                        apply int.modeq.modeq_mul;
                        try {assumption};
                        refl,
                end,
                tauto,
            end,
        inv_mem' :=
            begin
                rintros A ⟨ _ , A₀₁ , A₁₀ ⟩,
                split,
                {
                    rw inverse₀₀,
                    apply principal_condition₁₁,
                    split;
                    assumption,
                },
                {
                    rw inverse₀₁,
                    have := modeq_mul_left (-1:ℤ) A₀₁ ,
                    norm_num at this,
                    finish,
                },
                    rw inverse₁₀,
                    have := modeq_mul_left (-1:ℤ) A₁₀ ,
                    norm_num at this,
                    finish,
            end,
    }

    
end special_linear_group

end congruence_subgroups

open special_linear_group
    -- this notation includes parentheses so Γ is free for later use
notation `Γ(`N`)` := @principal_congurence_subgroup N _

/--
        A congruence subgroup is a subgroup Γ ≤ SL₂(ℤ) such that
                                Γ(N) ≤ Γ ≤ SL₂(ℤ)  for some N ≥ 1   
 -/
--    class CongruenceSubgroup(Γ : subgroup SL₂(ℤ)):=
--        (N: nat)
--        [hN: fact(0 < N)]
--        (contains_principal_congruence_subgroup: @principal_congurence_subgroup N hN ≤ Γ)
--                                        -- I would like to write something like Γ(N) ≤ Γ)
  