import main

open_locale classical

-- Example 3: A candidate x defeats a candidate y in P 
-- just in case the margin of x over y is (i) positive and 
-- (ii) greater than the weakest margin in each majority cycle containing x and y. 
def split_cycle_CCR {V X : Type} : CCR V X :=
    λ (P : Prof V X) (x y : X), ∀ [f: fintype V],
    @margin_pos V X f P x y ∧
    ¬ (∃ (c : list X), x ∈ c ∧ y ∈ c ∧
    cycle (λ a b, @margin V X f P x y ≤ @margin V X f P a b) c)

-- Example 4
def split_cycle_VCCR : VCCR := λ V X, split_cycle_CCR

/-def split_cycle_VCCR : VCCR := 
    λ V X (P : Prof V X) (x y : X), ∀ [f : fintype V], @margin_pos V X f P x y ∧ ¬ (∃ (c : list X), x ∈ c ∧ y ∈ c ∧ cycle (λ a b, @margin V X f P x y <= @margin V X f P a b) c)
-/

def split_cycle_VCCR' : VCCR := 
    λ V X (P : Prof V X) (x y : X), ∀ [f : fintype V], @margin_pos V X f P x y ∧ ¬ (∃ (c : list X) (e : c ≠ list.nil), c.nodup ∧ c.nth_le 0 (list.length_pos_of_ne_nil e) = y ∧ c.last e = x ∧ list.chain' (λ a b, @margin V X f P x y <= @margin V X f P a b ) c) 


-- Example 5: The Split Cycle voting method is 
-- the induced VSCC from the Split Cycle VCCR
def split_cycle : VSCC := max_el_VSCC split_cycle_VCCR

variables {V X : Type} 

lemma split_to_margin [fintype V] (P : Prof V X) (x y : X) : split_cycle_VCCR V X P x y → margin_pos P x y :=
begin
    unfold split_cycle_VCCR,
    unfold margin_pos,
    intro p,
    cases p with p_left p_right,
    exact p_left,
end

lemma split_cycle_to_margin_cycle [fintype V] (c : list X) (P : Prof V X) : cycle (split_cycle_VCCR V X P) c → cycle (margin_pos P) c :=
begin
    intro chain,
    unfold cycle at chain,
    cases chain with witness chain,
    use witness,
    refine list.chain_of_chain_map id _ _, 
    exact (split_cycle_VCCR V X P),
    intros a b s,
    exact and.left s,
    simp,
    exact chain,
end

lemma nonempty_ico {X : Type} (c : list X) (e : 0 < c.length) : (finset.Ico 0 c.length).nonempty  :=
begin
    fconstructor,
    use 0,
    simp at *,
    omega,
end

lemma lemma1 (x : ℕ) (y : ℕ) : x > 1 →  y < x - 1 → y.succ < x := by omega
lemma lemma2 (x : ℕ) (y : ℕ) : x > 1 →  y.succ < x → y < x - 1 := by omega

lemma split_cycle_VCCR_asymmetric [fintype V] (P : Prof V X) : asymmetric (split_cycle_VCCR V X P) :=
begin
    intros a b,
    unfold split_cycle_VCCR,
    unfold split_cycle_CCR,
    intro w,
    cases w with m _,
    push_neg,
    use _inst_1,
    intro m2,
    unfold margin_pos at *,
    rw margin_antisymmetric at m,
    exfalso,
    rw lt_neg at m,
    rw neg_zero at m,
    exact (not_lt_of_lt m) m2,
end

lemma split_cycle_VCCR_acyclic [fintype V] (P : Prof V X) : acyclic (split_cycle_VCCR V X P) :=
begin
    intros c a,
    have cy := a,
    cases a with e a,
    have f := nonempty_ico c (list.length_pos_of_ne_nil e),
    have b := split_cycle_to_margin_cycle c P cy,
    have x := finset.exists_min_image (finset.Ico 0 c.length) (λ x, (margin P) 
        (c.nth_le (x % c.length) (nat.mod_lt x (list.length_pos_of_ne_nil e))) 
        (c.nth_le ((x+1) % c.length) (nat.mod_lt (x+1) (list.length_pos_of_ne_nil e)))) f,
    cases x with mini_idx mini_req,
    cases mini_req with bounds mini_req,
    simp at bounds,
    let mini := (c.nth_le mini_idx bounds),
    have mini_mem := list.nth_le_mem c mini_idx bounds,
    have defeats := dominates_of_cycle_index c (split_cycle_VCCR V X P) cy mini_idx bounds,
    cases defeats with defeated defeats,
    simp at mini_req,
    contrapose defeats,
    push_neg,
    use c,
    use mini_mem,
    split,
    exact list.nth_le_mem c ((mini_idx + 1) % c.length) (nat.mod_lt (mini_idx + 1) (list.length_pos_of_ne_nil e)),
    unfold cycle,
    use e,
    rw list.chain_iff_nth_le,
    split,
    intro h,
    specialize mini_req (c.length - 1),
    have o : ∀ (n : ℕ), (0 < n) → n - 1 < n := by omega,
    specialize mini_req (o c.length h),
    have cal : (c.length-1) % c.length = c.length-1,
    apply nat.mod_eq_of_lt,
    exact o c.length h,
    simp_rw cal at mini_req,
    have cal : (c.length - 1 + 1) % c.length = 0,
    rw succ_pred h,
    exact nat.mod_self c.length,
    simp_rw cal at mini_req,
    rw ←list.last_eq_nth_le c e at mini_req,  
    have test : (margin P (c.nth_le (mini_idx % c.length) (mini_idx.mod_lt (list.length_pos_of_ne_nil e))) (c.nth_le ((mini_idx + 1) % c.length) ((mini_idx + 1).mod_lt (list.length_pos_of_ne_nil e))) ≤ margin P (c.last e) (c.nth_le 0 (eq.rec ((c.length - 1 + 1).mod_lt (list.length_pos_of_ne_nil e)) cal))) = (margin P (c.nth_le mini_idx bounds) (c.nth_le ((mini_idx + 1) % c.length) ((mini_idx + 1).mod_lt (length_cycle_pos cy))) ≤ margin P (c.last e) (c.nth_le 0 h)),
    congr,
    exact nat.mod_eq_of_lt bounds,
    rw ←test,
    exact mini_req,
    
    intros i h,
    specialize mini_req i,
    specialize mini_req (nat.lt_of_lt_pred h),
    simp_rw (nat.mod_eq_of_lt bounds) at mini_req,
    simp_rw (nat.mod_eq_of_lt (nat.lt_of_lt_pred h)) at mini_req,
    have o : ∀ i n, i < n - 1 → 0 < n → (i + 1) < n := by omega,
    simp_rw (nat.mod_eq_of_lt (o i c.length h (list.length_pos_of_ne_nil e))) at mini_req,
    exact mini_req,
end

lemma forall_take_while (l : list X) (P) : ∀ a ∈ (l.take_while P), P a :=
begin
    intro a,
    intro a_mem,
    induction l,
    obviously,

    change a ∈ if (P l_hd) then (l_hd :: list.take_while P l_tl) else list.nil at a_mem,
    by_cases (P l_hd),
    have i : ¬ (P l_hd) → list.nil = (l_hd :: list.take_while P l_tl),
    intro contr,
    exfalso,
    exact contr h,
    have test := ite_eq_left_iff.mpr i,
    rw test at a_mem,
    rw list.mem_cons_iff a l_hd (list.take_while P l_tl) at a_mem,
    cases a_mem,
    rw ←a_mem at h,
    exact h,
    exact l_ih a_mem,

    have i : (P l_hd) → (l_hd :: list.take_while P l_tl) = list.nil,
    intro contr,
    exfalso,
    exact h contr,
    have test := ite_eq_right_iff.mpr i,
    rw test at a_mem,
    exfalso,
    exact (list.not_mem_nil a) a_mem,
end

lemma nodup_of_nodup_take_while (X : Type) (l : list X) (P : X → Prop): l.nodup → (l.take_while P).nodup :=
begin
    intro a,
    have b := list.take_while_append_drop P l,
    refine list.nodup_of_nodup_append_left _,
    exact list.drop_while P l,
    rw b,
    exact a,
end

lemma rotate'_ne_nil_of_ne_nil {l : list X} {n : ℕ} : l ≠ list.nil → l.rotate' n ≠ list.nil :=
begin
    intro e,
    apply list.ne_nil_of_length_pos,
    rw list.length_rotate',
    apply list.length_pos_of_ne_nil,
    exact e,
end

theorem split_cycle_definitions : split_cycle_VCCR = split_cycle_VCCR' :=
begin
    ext1 V, ext1 X, ext1 P, ext1 x, ext1 y, 
    unfold split_cycle_VCCR, unfold split_cycle_VCCR', unfold split_cycle_CCR,
    simp, 
    split,
    intro permissive,
    introI _inst_1,
    split,
    cases permissive with margincond permissive,
    exact margincond,
    intro l,
    cases permissive with margincond permissive,
    specialize permissive l,
    intro nodup,
    intro ne_nil,
    by_contradiction,
    push_neg at h,
    cases h with first h,
    cases h with last h,
    have x_mem : x ∈ l,
    rw ←last,
    apply list.last_mem,
    specialize permissive x_mem,
    have y_mem : y ∈ l,
    rw ← first,
    apply list.nth_le_mem,
    specialize permissive y_mem,
    unfold cycle at permissive,
    push_neg at permissive,
    specialize permissive ne_nil,
    contrapose permissive,
    push_neg,
    rw list.chain_iff_nth_le,
    split,
        {intro h,
        rw last,
        rw first,},

        {intros i e,
        rw list.chain'_iff_nth_le at h,
        specialize h i,
        specialize h e,
        exact h,},

    intro restrictive,
    introI _inst_1,
    cases restrictive with margincond restrictive,
    use margincond,
    intros c x_mem y_mem ne_nil,
    have cy := ne_nil,
    cases ne_nil with ne_nil unused,
    let l₂ := c.rotate' (c.index_of y),
    let l₃ := l₂.take (l₂.index_of x + 1),
    let l := to_path l₃,

    specialize restrictive l,
    specialize restrictive (to_path_nodup l₃),

    have ne_nil2 : l ≠ list.nil,
        {by_contradiction,
        push_neg at h,
        have c_nil := (rotate'_eq_nil_iff X c (list.index_of y c)).mp,
        have l₃_nil : l₃ = list.nil := (to_path_eq_nil_iff l₃).mp h,
        have test := list.length_take (list.index_of x l₂ + 1) l₂,
        rw (list.length_eq_zero).mpr l₃_nil at test,
        have test2 := (min_choice (list.index_of x l₂ + 1) l₂.length),
        rw ←test at test2,
        cases test2,
        change 0 = (list.index_of x l₂).succ at test2,
        have test2 := eq.symm test2,
        exact (nat.succ_ne_zero (list.index_of x l₂)) test2,
        
        rw list.length_rotate' c (list.index_of y c) at test2,
        have test2 := eq.symm test2,
        exact ne_nil (list.length_eq_zero.mp test2),},
    
    specialize restrictive ne_nil2,
    contrapose restrictive,
    simp at *,
    split,
        {rw to_path_first_elem,
        rw list.nth_le_take',
        change (c.rotate' (list.index_of y c)).nth_le 0 _ = y,
        simp_rw ←list.rotate_eq_rotate',
        simp [list.rotate],
        rw list.nth_le_append,
        rw list.nth_le_drop',
        simp_rw nat.add_zero,
        simp_rw nat.mod_eq_of_lt (list.index_of_lt_length.mpr y_mem),
        refine list.index_of_nth_le
  (eq.rec
     (eq.rec (nat.add_lt_of_lt_sub_left (list.length_drop (list.index_of y c % list.length c) c ▸ _))
        (list.index_of y c % list.length c).add_zero)
     (nat.mod_eq_of_lt (list.index_of_lt_length.mpr y_mem))),
     
        rw list.length_drop,
        have o : ∀ (a b : ℕ), a < b → 0 < b - a := by omega,
        exact o (list.index_of y c % c.length) c.length (nat.mod_lt (list.index_of y c) (list.length_pos_of_ne_nil ne_nil)),
        exact (not_iff_not_of_iff (to_path_eq_nil_iff l₃)).mp ne_nil2,},

    split,
        {rw to_path_last_elem,
        rw list.last_eq_nth_le,
        rw list.nth_le_take',
        simp_rw list.length_take,
        
        have leq : (list.index_of x l₂ + 1) ≤ l₂.length,
        apply nat.lt_iff_add_one_le.mp,
        apply list.index_of_lt_length.mpr,
        change x ∈ c.rotate' (list.index_of y c),
        simp_rw ←list.rotate_eq_rotate',
        apply list.mem_rotate.mpr,
        exact x_mem,
        
        simp_rw min_eq_left leq,
        simp,
        exact (not_iff_not_of_iff (to_path_eq_nil_iff l₃)).mp ne_nil2,},

    apply to_path_chain'_of_chain',

    have l2_chain := rotate'_cycle_of_cycle ⟨ne_nil, unused⟩,
    cases l2_chain with _ l2_chain,

    exact chain'_take_of_chain (rotate'_ne_nil_of_ne_nil ne_nil) l2_chain,
end

lemma not_defeat_self [fintype V] (x : X) (P : Prof V X) : ¬ split_cycle_VCCR V X P x x := 
begin
    unfold split_cycle_VCCR,
    unfold split_cycle_CCR,
    push_neg,
    use _inst_1,
    intro a,
    exfalso,
    unfold margin_pos at a,
    rw self_margin_zero x P at a,
    linarith,
end