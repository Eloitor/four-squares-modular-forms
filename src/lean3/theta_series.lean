-- import data.finset.basic
-- import data.finset.lattice
-- import data.multiset.lattice
-- import topology.compacts
-- import topology.instances.complex
-- import data.int.basic
import data.finset
import tactic
import data.int.basic

/-
  Diamond - Shurman 
  exercise 4.9.2 (a)
-/

/--
  For each integer m, we define the set 
      
      { n ∈ `ℤᵈ   | max(n₁, ..., n_d) ≤ N }
-/
definition S' (N: ℕ ) (d: ℕ) : finset (fin d → ℤ) :=

  fintype.pi_finset (λ a, finset.Ico_ℤ (- N) (N+1))

/--
  For each integer m, we define the set 
      
      { n ∈ `ℤᵈ   | max(|n₁|, ..., |n_d|) = N}
-/
definition S (N: ℕ ) (d: ℕ) : finset (fin d → ℤ) :=
    finset.filter (λ n, ∃ (i : fin d), (n i).nat_abs = N) (S' N d)
     -- {n | ∀ i, (n i).nat_abs ≤ m  ∧ ∃ (i : fin d), n i = m}

definition S_aux (N: ℕ)(d:ℕ)(i: fin d): finset (fin d → ℤ) := 
  fintype.pi_finset (λ a, if a = i then {-N, N} else finset.Ico_ℤ (- N) (N+1))
  --finset.filter (λ n, (n i).nat_abs = N) (S' N d)    


lemma S_is_union (N: ℕ)(d: ℕ) : S N d =  finset.bind finset.univ (λ i, S_aux N d i):=
  begin
    ext1,
    split,
    {intro hx,
    norm_num at *,
    unfold S at *,
    simp at hx,
    cases hx,
    unfold S_aux,
    cases hx_right,
    use hx_right_w,
    simp,
    intro,
    split_ifs,
    unfold S' at *,
    norm_num,
    rw or_comm,
    rw ←hx_right_h,
    norm_num at *,
    specialize hx_left a_1,
    rw h,
    exact int.nat_abs_eq _,
    unfold S' at *,
    norm_num at *,
    specialize hx_left a_1,
    exact hx_left,
    },
    intro hx,
    unfold S_aux at *,
    unfold S,
    simp at *,
    split,
    unfold S',
    cases hx,
    norm_num,
    intro a1,
    specialize hx_h a1,
    by_cases a1=hx_w,
    --finish,
    split_ifs at *,
    norm_num at hx_h,
    cases hx_h,
    split,
    finish,
    linarith,
    split,
    linarith,
    linarith,
    split_ifs at *,
    norm_num at *,
    cases hx_h,
    split,
    linarith,
    linarith,
    cases hx,
    use hx_w,
    specialize hx_h hx_w,
    split_ifs at *,
    norm_num at hx_h,
    cases hx_h,
    finish,
    finish,
    norm_num at hx_h,
    cases hx_h,
    finish,
    finish,
  end


lemma S_aux_card (N: ℕ)(d: ℕ)(i: fin d): (S_aux N d i).card ≤ 2 * (2 * N + 1) ^ (d -1) :=
begin
    unfold S_aux,
    --norm_num,
    have : (λ (a : fin d), (ite (a = i) {-↑N, ↑N} (finset.Ico_ℤ (-↑N) (↑N + 1))).card) =
           λ (a : fin d), (ite (a = i) ({-↑N, ↑N}: finset ℤ).card (finset.Ico_ℤ (-↑N) (↑N + 1)).card),
      ext,
      split_ifs;
      refl,
    sorry
  /-  norm_num,
    rw this,
    simp,
    cases N,
    simp, -- N = 0 ⇒ {-N , N}.card = 1
    simp, -- N ≠ 0 ⇒ {-N , N}.card = 2
    have : (-1: ℤ) + -N ≠  ↑N + 1,
      linarith,
    have : ({-1 + -↑N, ↑N + 1}: finset ℤ).card = 2,
     finish,
    rw this,
    ring,
    have : finset.univ.prod (λ (x : fin d), ite (x = i) 2 ((2:ℤ) * ↑N + 3).to_nat) 
              = (finset.prod (finset.filter (λ (x : fin d), (x = i)) finset.univ) (λ a,2))
              * (finset.prod (finset.filter (λ (x : fin d), (x ≠ i)) finset.univ) (λ a,((2:ℤ) * ↑N + 3).to_nat)),
    {
      apply finset.prod_apply_ite _ _ (λ x, x),--(λ a,2)(λ a,((2:ℤ) * ↑N + 3).to_nat) (λ x,x),
    },
    rw this,
    simp,
    cases d,
    exact dec_trivial,
    refine le_of_eq _,
    congr,
    have : (finset.filter (λ (x : fin d.succ), x = i) finset.univ) = ({i}: finset (fin d.succ)),
      ext1,
      split,{
      norm_num},
      {
      intro ha,
      cases ha,
      norm_num,
      exact ha,
      norm_num,
      exfalso,
      cases ha,
      },
    rw this,
    norm_num,
    have : (finset.filter (λ (x : fin d.succ), x ≠ i) finset.univ) = ((finset.erase (finset.univ :finset (fin d.succ)) i)),
      ext1,
      split,{
      norm_num},
      {
      intro ha,
      norm_num at ha,
      norm_num,
      exact ha,
      },
    rw this,
    rw finset.card_erase_of_mem,
    norm_num,
    norm_num,
    -/
end


open_locale big_operators

open finset


lemma S_card_le (N: ℕ)(d: ℕ) :  finset.card (S N d) ≤ 2* d * (2 * N + 1) ^ (d -1) :=
begin
  calc finset.card (S N d) = finset.card (finset.bind finset.univ (λ i, S_aux N d i)) : by rw S_is_union N d
                  ...      ≤ ∑ i,           finset.card (S_aux N d i)                 : card_bind_le
                  ...      ≤  ∑ i:fin d,     2*(2*N+1)^(d-1)                          : sorry -- sum_le_sum (λ x hx, S_aux_card N d x)
                  ...      = 2*d*(2*N+1)^(d-1)                                        : by finish
end