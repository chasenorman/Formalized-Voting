import main
import split_cycle
import algebra.linear_ordered_comm_group_with_zero

open_locale classical 

variables {V X : Type}

def pareto (F : VSCC) (P : Prof V X ) : Prop := ∀ x y, ((∀ v, P v x y) → y ∉ F V X P)
 
lemma unanimous_margin [fintype V] [inhabited V] (P : Prof V X) [profile_asymmetric P] (x y : X) : (∀ v, P v x y) → margin_pos P x y :=
begin
    intro r,
    unfold margin_pos, unfold margin,
    classical,
    simp,
    have empty : (finset.filter (λ (x_1 : V), P x_1 y x) finset.univ).card = 0,
    apply finset.card_eq_zero.mpr, 
    apply finset.eq_empty_iff_forall_not_mem.mpr,
    simp,
    intro v,
    have b := (_inst_3.asymmetric),
    specialize b v,
    specialize r v,
    specialize b x, specialize b y,
    exact b r,
    rw empty,
    apply zero_lt_iff.mpr,
    by_contradiction a,
    push_neg at a,
    have a := finset.card_eq_zero.mp a,
    have a := finset.eq_empty_iff_forall_not_mem.mp a,
    simp at a,
    specialize a (_inst_2.default),
    specialize r (_inst_2.default),
    exact a r,
end


lemma ineq6 (a b : ℤ) : a > b → a - b > 0  := by omega

lemma ineq7 (n : ℕ) : n > 0 → n - 1 < n := by omega

lemma ineq8 (n : ℕ) : n > 1 → (n - 1) ≠ 0 := by omega

lemma preference_acyclic_ineq (i n : ℕ) : i.succ < n → 0 < n - 1 := by omega
lemma preference_acyclic_ineq2 (i n : ℕ) : ¬ (i = 0) → (i.succ < n → i < n - 1) := by omega

def preference_acyclic (P : Prof V X) [profile_irreflexive P] [profile_transitive P] (v : V) : ¬ ∃ (l : list X), cycle (P v) l :=
begin
    by_contradiction a,
    cases a with l a,
    cases a with e a,
    rw list.chain_iff_pairwise at a,
    obviously,
    specialize a_left (l.last e),
    specialize a_left (list.last_mem e),
    have irrefl := _inst_1.irreflexive,
    specialize irrefl v,
    specialize irrefl (l.last e),
    exact irrefl a_left,

    have transitive := _inst_2.transitive,
    specialize transitive v,
    exact transitive ᾰ ᾰ_1,
end

lemma ineq9 (a b c : ℕ) : (a:ℤ) ≤ ↑b - ↑c → a ≤ b :=
begin
    intro a,
    have : (0:ℤ) ≤ c := int.coe_zero_le c,
    linarith,
end

def split_cycle_pareto [inhabited V] [fintype V] (P : Prof V X) [profile_asymmetric P] [profile_transitive P] : pareto split_cycle P :=
begin
    intros x y r,
    unfold split_cycle,
    unfold max_el_VSCC,
    simp,
    use x,
    unfold split_cycle_VCCR, unfold split_cycle_CCR,
    simp,
    introI _inst_10,
    split,
    exact unanimous_margin P x y r,

    intro c, intro x_mem, intro y_mem,

    by_contradiction a, -- suppose there is a "defending" cycle where x dominates y.
    cases a with e b,

    have pc : cycle (P _inst_1.default) c, -- show that the guaranteed voter has a cyclic preference
    unfold cycle,
    use e, -- since c is a cycle in dominate, it is of length ≠ 0.

    have everyone_prefers : margin P x y = fintype.card V, -- we will show that the margin is |V|
    unfold margin,
    haveI _inst_4 : fintype ↥{v : V | P v y x} := subtype.fintype (λ v, P v y x),
    have nobody : ((finset.filter (λ (v : V), P v y x) finset.univ).card) = 0, -- first, nobody prefers y to x.
    rw finset.card_eq_zero,
    apply finset.eq_empty_iff_forall_not_mem.mpr,
    simp,
    intro x_1,
    have asymm := _inst_3.asymmetric,
    specialize asymm x_1 x y (r x_1), -- we know this because of profile asymmetry
    exact asymm, -- thus nobody prefers y to x
    simp at nobody,
    rw nobody,
    simp, -- now we need to show that the cardinality of those that prefer x to y is the cardinality of V
    rw (eq.symm finset.card_univ),
    have everyone : (finset.filter (λ (x_1 : V), P x_1 x y) finset.univ) = finset.univ,
    refine finset.ext_iff.mpr _,
    simp,
    exact r,
    rw everyone,

    refine list.chain.imp _ b,
    intros z w,
    rw everyone_prefers,
    intro b',
    unfold margin at b',
    have b' := ineq9 (fintype.card V) ((finset.filter (λ (x : V), P x z w) finset.univ).card) ((finset.filter (λ (x : V), P x w z) finset.univ).card) b',
    contrapose b',
    simp,
    rw finset.card_lt_iff_ne_univ,
    contrapose b',
    push_neg at b', push_neg,
    rw finset.eq_univ_iff_forall at b',
    simp at b',
    exact b' (default V),
    
    haveI irrefl := irreflexive_of_asymmetric P,
    have acyclic := preference_acyclic P (default V),
    have exists_cycle : ∃ (l : list X), cycle (P (default V)) l, 
    use c,
    exact pc,
    exact acyclic exists_cycle,
end