import main
import split_cycle
import algebra.linear_ordered_comm_group_with_zero
open_locale classical

variables {V X : Type}

def simple_lift : Prof V X → Prof V X → X → Prop := 
    λ P' P x, (∀ (a ≠ x) (b ≠ x) i, P i a b ↔ P' i a b) 
    ∧ ∀ a i, ((P i x a → P' i x a) ∧ (P' i a x → P i a x)) 

def monotonicity (F : VSCC) (P P' : Prof V X) : Prop := 
    ∀ (x ∈ F V X P), simple_lift P' P x → x ∈ F V X P'

lemma cardinality_lemma [fintype V] (p q : V → Prop) : (∀ v, (p v → q v)) → ((finset.filter p finset.univ).card ≤ (finset.filter q finset.univ).card) :=
begin
    intro pq,
    have subset : (finset.filter p finset.univ) ⊆ (finset.filter q finset.univ),
    refine finset.subset_iff.mpr _,
    simp,
    exact pq,
    exact (finset.card_le_of_subset subset),
end

lemma cardinality_lemma2 [fintype V] (p q : V → Prop) : (∀ v, (p v ↔ q v)) → ((finset.filter p finset.univ).card = (finset.filter q finset.univ).card) :=
begin
    intro pq,
    congr,
    ext1, simp at *, fsplit, work_on_goal 0 { intros ᾰ }, work_on_goal 1 { intros ᾰ },
    specialize pq x,
    exact pq.mp ᾰ,
    specialize pq x,
    exact pq.mpr ᾰ,
end

lemma margin_lemma (P P' : Prof V X) [fintype V] [profile_asymmetric P'] (a b : X) : (a ≠ b) → (∀ (v : V), (P v a b → P' v a b) ∧ (P' v b a → P v b a)) → margin P a b ≤ margin P' a b :=
begin
    intro h,

    intro lift,
    unfold margin,
    have first : ((finset.filter (λ (x_1 : V), P x_1 a b) finset.univ).card) ≤ ((finset.filter (λ (x_1 : V), P' x_1 a b) finset.univ).card),
    have first_pq : ∀ v, (λ (x_1 : V), P x_1 a b) v → (λ (x_1 : V), P' x_1 a b) v,
    simp,
    intro v, specialize lift v,
    cases lift with lift1 lift2,
    exact lift1,
    exact cardinality_lemma (λ (x_1 : V), P x_1 a b) (λ (x_1 : V), P' x_1 a b) first_pq,
    have second : ((finset.filter (λ (x_1 : V), P' x_1 b a) finset.univ).card) ≤ ((finset.filter (λ (x_1 : V), P x_1 b a) finset.univ).card),
    have second_pq : ∀ v, (λ (x_1 : V), P' x_1 b a) v → (λ (x_1 : V), P x_1 b a) v,
    simp,
    intro v,
    contrapose,
    intro npyx,
    specialize lift v,
    cases lift with lift1 lift2,
    contrapose npyx,
    push_neg, push_neg at npyx,
    exact lift2 npyx,

    exact cardinality_lemma (λ (x_1 : V), P' x_1 b a) (λ (x_1 : V), P x_1 b a) second_pq,
    mono,
    simp,
    exact first,
    simp,
    exact second,
end

-- if the elements are the same between the two Profs, the a = b case is still true.
lemma margin_lemma' (P P' : Prof V X) [fintype V] [profile_asymmetric P'] (a b : X) : (∀ (v : V), (P v a b → P' v a b) ∧ (P' v b a → P v b a)) → margin P a b ≤ margin P' a b :=
begin
    intro pq,
    by_cases a = b,
    rw h, 
    rw self_margin_zero, rw self_margin_zero,
    exact margin_lemma P P' a b h pq,
end


lemma margin_lt_margin_of_lift (P P' : Prof V X) [fintype V] [profile_asymmetric P'] (y x : X) : simple_lift P' P x → margin P' y x ≤ margin P y x :=
begin
    intro lift,
    unfold simple_lift at lift,
    cases lift with lift1 lift2, 
    specialize lift2 y,
    by_cases x = y,
    rw h, rw self_margin_zero, rw self_margin_zero,

    have test := margin_lemma P P' x y h lift2,
    rw margin_antisymmetric,
    rw margin_antisymmetric P,
    simp,
    exact test,
end

theorem split_cycle_monotonicity [fintype V] (P P' : Prof V X) [profile_asymmetric P'] : monotonicity split_cycle P P' :=
begin
    unfold monotonicity, intros x x_won lift, 
    unfold split_cycle, unfold max_el_VSCC, 
    rw split_cycle_definitions,
    simp,
    unfold split_cycle_VCCR', 
    intro y,
    push_neg, 
    use _inst_1,
    intro m, /- "so suppose margin P'(y,x) > 0." -/ 
    unfold split_cycle at x_won, 
    unfold max_el_VSCC at x_won, 
    rw split_cycle_definitions at x_won,
    simp at x_won,
    unfold split_cycle_VCCR' at x_won,
    simp at x_won, specialize x_won y, -- now we must show that there is a chain from x to y of margin greater than margin y x
    
    unfold margin_pos at m,
    have m' := margin_lt_margin_of_lift P P' y x lift,

    cases x_won with _ x_won,
    unfold margin_pos at x_won,
    rw margin_eq_margin x_won_w _inst_1 at x_won, 

    specialize x_won (lt_of_lt_of_le m m'),
    cases x_won with l x_won,
    use l,
    cases x_won with nodup x_won,
    cases x_won with nonempty x_won,
    use nonempty,
    use nodup,
    cases x_won with x_nth x_won,
    use x_nth,
    cases x_won with y_nth x_won,
    use y_nth, -- reduced to just the chain. All the properties of the chain have been proven.

    rw list.chain'_iff_nth_le at x_won,
    rw list.chain'_iff_nth_le, 
    intro i, intro i_bound, -- for any index i
    specialize x_won i,
    specialize x_won i_bound,
    have test := le_trans m' x_won,
    apply le_trans test, -- by the transitive property it is sufficient to show that the margins exclusively increased due to the lift.

    -- problem: if the cycle is not simple and contains x, it may not be a cycle in P'.  
    by_cases i = 0,
    have eq : (l.nth_le i (nat.lt_of_lt_pred i_bound)) = (l.nth_le 0 (list.length_pos_of_ne_nil nonempty)),
    congr, exact h,
    rw eq, rw x_nth,
    cases lift with lift1 lift2,
    rw margin_eq_margin x_won_w _inst_1,
    exact margin_lemma' P P' x (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound)) (lift2 (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound))), 
    -- we use the second property of lifts to show this since the first element is x.

    have neq : (l.nth_le i (nat.lt_of_lt_pred i_bound)) ≠ x, 
    change l.pairwise ne at nodup,
    rw ←x_nth,
    exact ne.symm (list.pairwise_iff_nth_le.mp nodup 0 i (nat.lt_of_lt_pred i_bound) (zero_lt_iff.mpr h)),

    have neq2 : (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound)) ≠ x,
    change l.pairwise ne at nodup,
    rw ←x_nth,
    exact ne.symm (list.pairwise_iff_nth_le.mp nodup 0 (i + 1) (nat.lt_pred_iff.mp i_bound) (nat.zero_lt_succ i)),

    have pq : ∀ (v : V),
    (P v (l.nth_le i (nat.lt_of_lt_pred i_bound)) (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound)) → P' v (l.nth_le i (nat.lt_of_lt_pred i_bound)) (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound))) ∧
      (P' v (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound)) (l.nth_le i (nat.lt_of_lt_pred i_bound)) → P v (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound)) (l.nth_le i (nat.lt_of_lt_pred i_bound))),

    intro v,
    cases lift with lift1 lift2,
    split,
    exact (lift1 (l.nth_le i (nat.lt_of_lt_pred i_bound)) neq (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound)) neq2 v).mp,
    exact (lift1 (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound)) neq2 (l.nth_le i (nat.lt_of_lt_pred i_bound)) neq v).mpr,
    rw margin_eq_margin x_won_w _inst_1,
    exact margin_lemma' P P' (l.nth_le i (nat.lt_of_lt_pred i_bound)) (l.nth_le (i + 1) (nat.lt_pred_iff.mp i_bound)) pq,
end