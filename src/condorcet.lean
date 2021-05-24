import main
import split_cycle 

open_locale classical

variables {V X : Type}

def condorcet_winner [fintype V] (P : Prof V X) (x : X) : Prop := ∀ y, x ≠ y → margin_pos P x y

--def condorcet_winner [fintype V] (P : Prof V X) (x : X) : Prop := ∀ y ≠ x, margin_pos P x y

def condorcet_loser [fintype V] (P : Prof V X) (x : X) : Prop := (∀ y, x ≠ y → margin_pos P y x) ∧ ∃ y, x ≠ y

def condorcet_criterion [fintype V] (F : VSCC) (P : Prof V X) : Prop := ∀ x, condorcet_winner P x → F V X P = {x}

def condorcet_loser_criterion [fintype V] (F : VSCC) (P : Prof V X) : Prop := ∀ x, condorcet_loser P x → x ∉ F V X P

lemma ineq {n : ℕ} (e : n > 1) : (n - 2).succ < n := by omega
lemma ineq2 {n : ℕ} (e : n > 1) : (n - 2).succ = (n - 1) := by omega

lemma gt_zero_of_ne_zero (i : ℕ) : i ≠ 0 → i > 0 := by omega

def condorcet_SCC [fintype V] : SCC V X := λ P, if c : (∃x, condorcet_winner P x) then {c.some} else set.univ

def condorcet_VSCC : VSCC := λ V X P, if f : (∃ [fintype V], true) then @condorcet_SCC V X f.some P else ∅

def split_cycle_condorcet_criterion [fintype V] (P : Prof V X) : condorcet_criterion split_cycle P := 
begin
    intro w,
    intro x_winner,
    unfold split_cycle, 
    unfold split_cycle_VCCR,
    unfold split_cycle_CCR,
    unfold max_el_VSCC,
    simp,

    have no_cycles : ¬ ∃ l (e : cycle (margin_pos P) l), w ∈ l,
    by_contradiction a,
    cases a with l a,
    cases a with e a,
    have defeated := dominate_of_cycle l (margin_pos P) e w a, 
    cases defeated with bad defeated,
    cases defeated with _ defeated,
    specialize x_winner bad,
    have ne : w ≠ bad,
    simp,
    by_contradiction a_1,
    rw a_1 at defeated,
    unfold margin_pos at defeated,
    rw self_margin_zero bad P at defeated,
    linarith,
    specialize x_winner ne,
    unfold margin_pos at *,
    have as := margin_antisymmetric P,
    unfold antisymmetric at as,
    specialize as bad w,
    rw as at defeated,
    linarith,
    
    ext1,
    split,
    intro a,
    specialize a w,
    apply of_not_not,
    by_contradiction a_1,
    specialize x_winner x,
    have x_winner := x_winner (ne.symm a_1),
    cases a with f a,
    unfold margin_pos at a,
    rw margin_eq_margin f _inst_1 P w x at a,
    have a := a x_winner,
    cases a with c a,
    cases a with w_mem a,
    cases a with x_mem cy,
    have contr : ∃ (l : list X) (e : cycle (margin_pos P) l), w ∈ l,
    use c,
    refine and.intro _ w_mem,
    have imp : ∀ e1 e2, (λ (a b : X), margin P w x ≤ margin P a b) e1 e2 → (margin_pos P) e1 e2,
        {intros e1 e2,
        simp,
        intro z,
        have o : ∀ (a b : ℤ), a > 0 → a ≤ b → b > 0 := by omega,
        exact o (margin P w x) (margin P e1 e2) x_winner z,},
    simp_rw margin_eq_margin f _inst_1 at cy,
    exact cycle_of_cycle_imp imp cy,
    
    exact no_cycles contr,
    
    intro eq,
    intro x_1,
    by_contradiction a,
    push_neg at a,
    specialize a _inst_1,
    cases a with a b,
    simp at eq,
    rw eq at a,
    specialize x_winner x_1,
    by_cases eq : x_1 = w,
    rw eq at a,
    unfold margin_pos at a,
    rw self_margin_zero w P at a,
    linarith,

    specialize x_winner (ne.symm eq),
    unfold margin_pos at *,
    have as := margin_antisymmetric P,
    unfold antisymmetric at as,
    specialize as x_1 w,
    rw as at a,
    linarith,
end

lemma margin_pos_irrefl [fintype V] (P : Prof V X) : ∀ x, ¬ margin_pos P x x :=
begin
    intro x, -- for any candidate x
    unfold margin_pos,
    unfold margin,
    linarith, 
end

-- we should probably get the axioms out of the way for this. Is it a strict total order? 
lemma margin_pos_asymm [fintype V] (P : Prof V X) : ∀ x y, margin_pos P x y → ¬ margin_pos P y x :=
begin
    intro x, intro y,
    unfold margin_pos,
    unfold margin,
    intro dominates,
    push_neg,
    linarith,
end


lemma condorcet_loser_ineq (a : ℤ) : (0 < a) → (-a ≤ 0) := by omega

def split_cycle_condorcet_loser_criterion [fintype V] (P : Prof V X) : condorcet_loser_criterion split_cycle P :=
begin
    intro x,
    intro x_loser,
    unfold split_cycle,
    unfold max_el_VSCC,
    simp,
    unfold condorcet_loser at x_loser,
    cases x_loser with a b,
    cases b with y b, -- consider the element y ≠ x guaranteed by condorcet_loser.
    use y, -- we will prove this element defeats x.
    unfold split_cycle_VCCR,
    introI _inst_2,
    split,
    unfold margin_pos,
    rw margin_eq_margin _inst_2 _inst_1,
    exact a y b,
    by_contradiction, -- we show there is no clemency cycle by contradiction
    cases h with l h,
    cases h with y_mem h,
    cases h with x_mem c,
    have dominates := dominates_of_cycle l (λ (a b : X), margin P y x ≤ margin P a b) c x x_mem,
    cases dominates with z dominates, -- let z be the element dominated by x
    cases dominates with z_mem dominates,
    have contr : margin P x z ≤ 0,
    specialize a z, 
    by_cases x = z,
    rw h,
    rw self_margin_zero,
    specialize a h,
    unfold margin_pos at a,
    rw margin_antisymmetric,
    rw margin_eq_margin _inst_2 _inst_1,
    exact condorcet_loser_ineq (@margin V X _inst_1 P z x) a,
    have f := int.le_trans dominates contr,
    specialize a y, specialize a b,
    unfold margin_pos at a,
    rw margin_eq_margin _inst_2 _inst_1 at f,
    exact (not_lt.mpr f) a,
end