import tactic
import data.list.chain
import data.fintype.basic
import data.list.rotate
import data.list.basic
import tactic.omega
import data.nat.modeq
import tactic.zify
import data.stream.basic

open_locale classical 
noncomputable theory

variables {X : Type}

def cycle := λ (P : X → X → Prop) (c : list X), ∃ (e : c ≠ list.nil), list.chain P (c.last e) c

def reverse := λ (P : X → X → Prop) (x y : X), P y x 

def length_cycle_pos {l : list X} {P : X → X → Prop} (c : cycle P l) : 0 < l.length :=
begin
    cases c with a b,
    exact list.length_pos_of_ne_nil a,
end

-- updated acyclic definition.
def acyclic : (X → X → Prop) → Prop := λ P, ∀ (c : list X), ¬ cycle P c

lemma size_lemma {x : ℕ} (l : list X) (y : x < l.reverse.length) : l.length - 1 - x < l.length :=
begin 
    rw list.length_reverse at y,
    omega,
end

lemma nth_reverse {x : ℕ} (l : list X) (y: x < l.reverse.length) : l.reverse.nth_le x y = l.nth_le (l.length - 1 - x) (size_lemma l y) :=
begin
    have to_use := eq.symm (list.nth_le_reverse l.reverse x _ _),
    rw to_use,
    simp,
    simp only [list.length_reverse],
    exact size_lemma l y,
end

lemma nonempty_last (l : list X) (e : l.length > 0) : l.reverse ≠ list.nil := 
begin
    rw eq.symm (list.length_reverse l) at e,
    exact list.ne_nil_of_length_pos e,
end

lemma last_reverse (l : list X) (e : l.length > 0) : l.reverse.last (nonempty_last l e) = l.nth_le 0 e :=
begin
    rw list.last_eq_nth_le,
    rw nth_reverse,
    have ineq : (l.length - 1 - (l.reverse.length - 1)) = 0,
    rw list.length_reverse,
    simp,
    simp,
end

lemma head'_eq_nth_le_zero (l : list X) (y : X) (e : l ≠ list.nil) : y ∈ l.head' → y = (l.nth_le 0 (list.length_pos_of_ne_nil e)) :=
begin
    intro a,
    obviously,
    rw ←list.nth_zero at a,
    rw list.nth_le_nth (list.length_pos_of_ne_nil e) at a,
    obviously,
end

lemma within_rotate_of_within {l : list X} {i : ℕ} (n : ℕ) (e : i < l.length) : i < (l.rotate n).length := by obviously

lemma ne_nil_of_lt_length {a b : ℕ} : a < b → b > 0 := by omega

lemma nth_le_rotate {l : list X} {n i : ℕ} (e : i < l.length) : ((l.rotate n).nth_le i (within_rotate_of_within n e)) = l.nth_le ((i + n) % l.length) (nat.mod_lt (i+n) (ne_nil_of_lt_length e)) :=
begin
    have first := list.nth_rotate e,
    work_on_goal 1 {exact n,},
    rw list.nth_le_nth (within_rotate_of_within n e) at first,
    rw list.nth_le_nth ((i + n).mod_lt (ne_nil_of_lt_length e)) at first,
    obviously,
end

lemma rotate1_cycle_of_cycle {a : X} {l : list X} {P : X → X → Prop} : cycle P (a :: l) → cycle P (l ++ [a]) :=
begin
    intro c,
    unfold cycle at *,
    cases c with _ c,
    obviously,
    change list.chain' P (a :: l ++ [a]),
    apply list.chain'.append,
    change list.chain' P (a :: l) at c_right,
    exact c_right,
    exact list.chain'_singleton a,
    intros x x_mem y y_mem,
    have i := list.mem_last'_eq_last x_mem,
    cases i with _ i,
    rw i,
    obviously,
end

-- proof by induction? cycle (a :: l) iff cycle (l ++ [a]), list.rotate_cons_succ
lemma rotate'_cycle_of_cycle {c : list X} {P : X → X → Prop} {n : ℕ} : cycle P c → cycle P (list.rotate' c n) :=
begin
    intro cy,
    induction n,
    rw list.rotate'_zero,
    exact cy,

    rw nat.succ_eq_add_one,
    rw ←list.rotate'_rotate',
    have i := n_ih,
    cases i with n _,
    have e := list.exists_cons_of_ne_nil n,
    cases e with a e,
    cases e with l e,
    rw e,
    rw list.rotate'_cons_succ,
    rw list.rotate'_zero,
    rw e at n_ih,
    exact rotate1_cycle_of_cycle n_ih,
end

lemma dominate_ineq1 (i n : ℕ) : ¬(i = 0) → (i < n → i - 1 < n - 1) := by omega
lemma dominate_ineq2 (i : ℕ) : ¬(i = 0) → (i - 1 + 1) = i := by omega
lemma ineq4 (i n : ℕ) (e : i < n) : i.pred < n := 
begin
    rw nat.pred_eq_sub_one i,
    omega,
end
lemma ineq5 (i n : ℕ) (e : i < n) (z: ¬i = n - 1) : i < n - 1 := by omega

-- every node in a cycle is defeated by some other node in that cycle.
lemma dominate_of_cycle (l : list X) (P : X → X → Prop) (c : cycle P l) : ∀ x ∈ l, ∃ y ∈ l, P y x :=
begin
    intro x, -- for any element x 
    intro mem, -- and a proof that x is in the list
    unfold cycle at c,
    cases c with e c,
    rw list.chain_iff_nth_le at c,
    cases c with c_right c_left,
    let i := l.index_of x,
    have i_bound : i < l.length,
    apply list.index_of_lt_length.mpr,
    exact mem,
    by_cases z : i = 0,
        {use (l.last e),
        use list.last_mem e,
        rw ←(list.index_of_nth_le i_bound),
        change P (l.last e) (l.nth_le i i_bound),
        simp_rw z,
        exact (c_right (eq.rec i_bound z)),},

        {use l.nth_le (i - 1) ((ineq4 i l.length) i_bound),
        use l.nth_le_mem (i - 1) ((ineq4 i l.length) i_bound),
        specialize c_left (i - 1),
        specialize c_left ((dominate_ineq1 i l.length) z i_bound),
        simp_rw (dominate_ineq2 i z) at c_left,
        rw ←(list.index_of_nth_le i_bound),
        change P (l.nth_le (i - 1) _) (l.nth_le i i_bound),
        exact c_left,},
end

lemma succ_pred {i : ℕ} (e : 0 < i) : i - 1 + 1 = i := by omega
lemma dominate_ineq3 {a b : ℕ} (e : 0 < b) : a < b - 1 → a + 1 < b := by omega
-- have defeats := dominates_of_cycle X c (split_cycle_VCCR_function V X P) cy mini mini_mem,
lemma dominates_of_cycle_index (l : list X) (P : X → X → Prop) (c : cycle P l) (i : ℕ) (i_bound : i < l.length) 
   : P (l.nth_le i i_bound) (l.nth_le ((i + 1) % l.length) (nat.mod_lt (i + 1) (length_cycle_pos c))) :=
begin
    unfold cycle at c,
    cases c with e c,
    rw list.chain_iff_nth_le at c,
    cases c with c_left c_right,
    by_cases z : i = l.length - 1,
        {simp_rw z, rw ←list.last_eq_nth_le l e,
        specialize c_left (list.length_pos_of_ne_nil e),
        simp_rw succ_pred (list.length_pos_of_ne_nil e),
        simp_rw nat.mod_self,
        exact c_left,},

    specialize c_right i,
    have i_bound2 := ineq5 i l.length i_bound z,
    specialize c_right i_bound2,
    have underflow : (i + 1) % l.length = (i + 1),
    rw nat.mod_eq_of_lt,
    exact dominate_ineq3 (list.length_pos_of_ne_nil e) i_bound2,
    simp_rw underflow,
    exact c_right,
end

lemma dominates_of_cycle (l : list X) (P : X → X → Prop) (c : cycle P l) : ∀ x ∈ l, ∃ y ∈ l, P x y :=
begin
    intro x,
    intro mem,
    let i := l.index_of x,
    have d := dominates_of_cycle_index l P c,
    specialize d i,
    specialize d (list.index_of_lt_length.mpr mem),
    use (l.nth_le ((i + 1) % l.length) ((i + 1).mod_lt (length_cycle_pos c))),
    split,
    apply list.nth_le_mem,
    simp_rw list.index_of_nth_le at d,
    exact d,
end

lemma cycle_reverse_in_reverse_relation (P : X → X → Prop) (l : list X) (c : cycle P l) : cycle (reverse P) (l.reverse) :=
begin
    obviously, -- handles proof of reverse ne nil,
    rw list.chain_iff_nth_le,
    rw list.chain_iff_nth_le at c_h,
    obviously, -- performs the necessary splitting and rewriting
    rw last_reverse l (list.length_pos_of_ne_nil c_w),
    rw nth_reverse,
    simp_rw nat.sub_zero,
    rw ←list.last_eq_nth_le,
    specialize c_h_left (list.length_pos_of_ne_nil c_w),
    exact c_h_left,

    rw nth_reverse,
    rw nth_reverse,
    simp [reverse],
    specialize c_h_right (l.length - 1 - (i + 1)),
    have o : ∀ n, (i < n - 1) → n - 1 - (i + 1) < n - 1 := by omega,
    specialize c_h_right (o l.length h),
    have o : ∀ n, (i < n - 1) → (n - 1 - (i + 1) + 1) = (n - 1 - i) := by omega,
    simp_rw (o l.length h) at c_h_right,
    exact c_h_right,
end

noncomputable def to_path : list X → list X
| list.nil := list.nil
| (list.cons u p) := 
    let p' := to_path p
    in if p'.index_of u < p'.length
        then (p'.drop (p'.index_of u))
        else (list.cons u p')

lemma ite_left_if {α : Type} {p : Prop} [decidable p] {a b : α} : p → ite p a b = a := by obviously
lemma ite_right_if {α : Type} {p : Prop} [decidable p] {a b : α} : ¬ p → ite p a b = b := by obviously

lemma nodup_drop_of_nodup {l : list X} {n : ℕ} : l.nodup → (l.drop n).nodup :=
begin
    by_cases n < l.length,
    rw list.nodup_iff_nth_le_inj,
    rw list.nodup_iff_nth_le_inj,
    intros a i j h₁ h₂,
    rw list.nth_le_drop',
    rw list.nth_le_drop',
    intro eq, 
    specialize a (n+i),
    specialize a (n+j),
    rw list.length_drop at h₁,
    rw list.length_drop at h₂,
    have o : ∀ (a b c : ℕ), c < b → a < b - c → c + a < b := by omega,
    specialize a (o i l.length n h h₁),
    specialize a (o j l.length n h h₂),
    specialize a eq,
    exact (add_right_inj n).mp a,

    push_neg at h,
    intro a,
    have sub : (list.drop n l).length = 0,
    rw list.length_drop,
    omega,
    rw (list.eq_nil_of_length_eq_zero sub),
    exact list.nodup_nil,
end

lemma to_path_nodup (l : list X) : (to_path l).nodup :=
begin
    induction l,
    exact list.nodup_nil,
    simp [to_path],
    
    by_cases (list.index_of l_hd (to_path l_tl) < (to_path l_tl).length),
    simp_rw (ite_left_if h),
    exact nodup_drop_of_nodup l_ih,

    simp_rw (ite_right_if h),
    have not_mem : l_hd ∉ (to_path l_tl),
    contrapose h,
    push_neg at h, push_neg,
    exact list.index_of_lt_length.mpr h,
    exact list.nodup_cons_of_nodup not_mem l_ih,
end

lemma to_path_eq_nil_iff (l : list X) : (to_path l) = list.nil ↔ l = list.nil :=
begin
    induction l,
    obviously,
    simp [to_path] at ᾰ,
    contrapose ᾰ,
    by_cases (list.index_of l_hd (to_path l_tl) < (to_path l_tl).length),
    apply list.ne_nil_of_length_pos,
    rw (ite_left_if h),
    rw list.length_drop,
    have ineq : ∀ (a b : ℕ), a < b → 0 < b - a := by omega,
    exact ineq (list.index_of l_hd (to_path l_tl)) ((to_path l_tl).length) h,
    rw (ite_right_if h),
    exact list.cons_ne_nil (l_hd) (to_path l_tl),
end

lemma helper (X : Type) (l : list X) (n : l ≠ list.nil) : 0 < (to_path l).length :=
begin
    apply list.length_pos_of_ne_nil,
    contrapose n,
    push_neg, push_neg at n,
    exact (to_path_eq_nil_iff l).mp n,
end

lemma to_path_first_elem (X : Type) (l : list X) (n : l ≠ list.nil) : (list.nth_le (to_path l) 0 (helper X l n)) = (list.nth_le l 0 (list.length_pos_of_ne_nil n)) :=
begin
    induction l,
    obviously,
    simp [to_path],
    by_cases (list.index_of l_hd (to_path l_tl) < (to_path l_tl).length),
    simp_rw (ite_left_if h),
    rw list.nth_le_drop',
    simp_rw nat.add_zero,
    rw list.index_of_nth_le,

    simp_rw (ite_right_if h),
    obviously,
end

lemma helper' (X : Type) (l : list X) (n: 0 < (to_path l).length) : l ≠ list.nil :=
begin
    contrapose n,
    push_neg at n,
    have a := (to_path_eq_nil_iff l).mpr n,
    contrapose a,
    push_neg at a,
    exact list.ne_nil_of_length_pos a,
end

lemma to_path_first_elem' (X : Type) (l : list X) (n : (to_path l).length > 0) : (list.nth_le (to_path l) 0 n) = (list.nth_le l 0 (list.length_pos_of_ne_nil (helper' X l n))) :=
begin
    induction l,
    obviously,
    simp [to_path],
    by_cases (list.index_of l_hd (to_path l_tl) < (to_path l_tl).length),
    simp_rw (ite_left_if h),
    rw list.nth_le_drop',
    simp_rw nat.add_zero,
    rw list.index_of_nth_le,

    simp_rw (ite_right_if h),
    obviously,
end

lemma to_path_ne_nil_iff (l : list X) (n : l ≠ list.nil) : (to_path l) ≠ list.nil :=
begin
    by_contradiction,
    push_neg at h,
    have test := (to_path_eq_nil_iff l).mp h,
    exact n test,
end

-- list.index_of l_hd (to_path l_tl) + ((to_path l_tl).length - list.index_of l_hd (to_path l_tl) - 1) = (to_path l_tl).length - 1
lemma last_elem_lemma {a b : ℕ} : (a < b) → a + (b - a - 1) = b - 1 := by omega


lemma to_path_last_elem (l : list X) (n : l ≠ list.nil) : ((to_path l).last (to_path_ne_nil_iff l n)) = (l.last n) :=
begin
    induction l,
    obviously,
    simp [to_path],
    by_cases (list.index_of l_hd (to_path l_tl) < (to_path l_tl).length),
    simp_rw (ite_left_if h),
    rw list.last_eq_nth_le,
    simp_rw list.length_drop,
    rw list.nth_le_drop',
    simp_rw last_elem_lemma h,
    have to_path_ne_nil : (to_path l_tl) ≠ list.nil,
    apply list.ne_nil_of_length_pos,
    have pos_of_lt : ∀ (a b : ℕ), a < b → 0 < b := by omega,
    exact pos_of_lt (list.index_of l_hd (to_path l_tl)) (to_path l_tl).length h,
    have to_path_ne_nil := (not_iff_not_of_iff (to_path_eq_nil_iff l_tl)).mp to_path_ne_nil,
    specialize l_ih to_path_ne_nil,
    rw ←list.last_eq_nth_le (to_path l_tl) (to_path_ne_nil_iff l_tl to_path_ne_nil),
    rw l_ih,
    exact (eq.symm (list.last_cons n to_path_ne_nil)),

    simp_rw (ite_right_if h),
    induction l_tl,
    obviously,
    rw list.last_cons,
    exact l_ih,
end

lemma drop_chain'_of_chain' {X : Type} {l : list X} {P : X → X → Prop} {n : ℕ} : l.chain' P → (l.drop n).chain' P :=
begin
    by_cases n < l.length,
    rw list.chain'_iff_nth_le, 
    rw list.chain'_iff_nth_le,
    intros a i t,
    rw list.nth_le_drop',
    rw list.nth_le_drop',
    rw list.length_drop at t,
    specialize a (n + i),
    have o : ∀ (n i l : ℕ), n < l → i < l - n - 1 → n + i < l - 1 := by omega,
    specialize a (o n i l.length h t),
    exact a,

    push_neg at h,
    intro a,
    have sub : (list.drop n l).length = 0,
    rw list.length_drop,
    omega,
    rw (list.eq_nil_of_length_eq_zero sub),
    exact list.chain'_nil,
end

lemma nth_le_cons {l : list X} {i : ℕ} {e : (i - 1) < l.length} {a : X} {p : i < (a :: l).length} (n : ¬ i = 0) : ((a :: l).nth_le i p) = (l.nth_le (i - 1) e) :=
begin
  let j := i - 1,
  change (a :: l).nth_le (i) p = l.nth_le j e,
  change (a :: l).nth_le (i) p = (a :: l).nth_le (j + 1) _,
  congr,
  change i = i - 1 + 1,
  omega,
  dsimp at *, simp at *, assumption,
end

lemma to_path_chain'_of_chain' {X : Type} {l : list X} {P : X → X → Prop} : list.chain' P l → list.chain' P (to_path l) :=
begin
    intro a,
    induction l,
    obviously,
    simp [to_path],
    specialize l_ih (and.right (list.chain'_cons'.mp a)),
    by_cases (list.index_of l_hd (to_path l_tl) < (to_path l_tl).length),
    simp_rw (ite_left_if h),
    exact drop_chain'_of_chain' l_ih,

    simp_rw (ite_right_if h),
    by_cases j : l_tl = list.nil,
    rw (to_path_eq_nil_iff l_tl).mpr j,
    exact list.chain'_singleton l_hd,

    rw list.chain'_iff_nth_le,
    rw list.chain'_iff_nth_le at l_ih,
    rw list.chain'_iff_nth_le at a,
    intros i i_bounds,
    by_cases i = 0,
    simp_rw h,
    rw [list.nth_le], rw [list.nth_le],
    specialize a 0,
    have a_proof : 0 < (l_hd :: l_tl).length - 1,
    rw list.length_cons,
    simp only [nat.add_succ_sub_one, add_zero],
    exact (list.length_pos_of_ne_nil j),
    specialize a a_proof,
    rw [list.nth_le] at a, rw [list.nth_le] at a,
    have x := (to_path_first_elem X l_tl j),
    have z : (to_path l_tl).nth_le 0 (helper X l_tl j) = (to_path l_tl).nth_le 0 (list.nth_le._main._proof_1 l_hd (to_path l_tl) 0
  (eq.rec (nat.lt_pred_iff.mp i_bounds)
     ((λ [c : has_add ℕ] (ᾰ ᾰ_1 : ℕ) (e_2 : ᾰ = ᾰ_1) (ᾰ_2 ᾰ_3 : ℕ) (e_3 : ᾰ_2 = ᾰ_3),
         congr (congr_arg has_add.add e_2) e_3) i 0 h 1 1 (eq.refl 1)))),
    refl,
    rw z at x,
    rw x,
    exact a,

    rw [list.nth_le],
    specialize l_ih (i - 1),
    rw list.length_cons at i_bounds,
    simp only [nat.add_succ_sub_one, add_zero] at i_bounds,
    have o : ∀ i n, ¬ i = 0 → i < n → i - 1 < n - 1 := by omega,
    specialize l_ih (o i (to_path l_tl).length h i_bounds),
    rw nth_le_cons h,
    have o : ∀ i, ¬ i = 0 → i - 1 + 1 = i := by omega,
    simp_rw (o i h) at l_ih,
    exact l_ih,
end

lemma rotate'_eq_nil_iff (X : Type) (l : list X) (n : ℕ) : l.rotate' n = list.nil ↔ l = list.nil :=
begin
    have a := list.length_eq_zero,
    work_on_goal 2 {
        exact l,
    },
    rw ←a,
    have a := list.length_eq_zero,
    work_on_goal 2 {
        exact l.rotate' n,
    },
    rw ←a,
    rw list.length_rotate' l n,
end

lemma cycle_of_cycle_imp {X : Type} {l : list X} {p₁ p₂ : X → X → Prop} (e : ∀ x y, p₁ x y → p₂ x y) : cycle p₁ l → cycle p₂ l :=
begin
    obviously,
    exact list.chain.imp e ᾰ_h,
end

lemma chain'_of_chain'_append {x : list X} {y : list X} {P : X → X → Prop} (e : list.chain' P (x ++ y)) : list.chain' P x :=
begin
    rw list.chain'_iff_nth_le, rw list.chain'_iff_nth_le at e,
    intros i h,
    specialize e i,
    have o : ∀ a b c, a < b - 1 → a < b + c - 1 := by omega,
    have t := (o i x.length y.length h),
    rw ←list.length_append at t,
    specialize e t,
    rw list.nth_le_append (nat.lt_of_lt_pred t) (nat.lt_of_lt_pred h) at e, 
    rw list.nth_le_append at e,
    exact e,
end

lemma chain'_take_of_chain {l : list X} {P : X → X → Prop} (a : l ≠ list.nil) {n : ℕ} (c : list.chain P (l.last a) l) : list.chain' P (l.take n) :=
begin
    change list.chain' P ((l.last a) :: l) at c,
    rw list.chain'_cons' at c,
    cases c with _ c, 
    rw ←(list.take_append_drop n l) at c,
    let y := (list.drop n l),
    change list.chain' P (list.take n l ++ y) at c,
    exact chain'_of_chain'_append c,
end

lemma nth_take_ineq {a b c : ℕ} (d : a < b) (e : c = b) : (a < c) :=
begin
    have e := eq.symm e,
    rw e at d,
    exact d,
end

lemma nth_take {X : Type} {n x : ℕ} (e : x < n) (s : stream X) : ((s.take n).nth_le x (nth_take_ineq e (s.length_take n))) = (s.nth x) :=
begin
    unfold stream.take,
    rw list.nth_le_map,
    rw list.nth_le_range,
    rw list.length_range,
    exact e,
end