import main
import split_cycle
import data.list.nodup
import tactic

open_locale classical
noncomputable theory

variables {V X : Type}

def minus_candidate (P : Prof V X) (b : X) : Prof V {x : X // x ≠ b} := λ v x y, P v x y

variables (P : Prof V X) (c : X) (D : set {x : X // x ≠ c})

def clones : Prop := D.nonempty ∧ (∀ (c' ∈ D) (x : {x : X // x ≠ c}) (i : V), x ∉ D → ((P i c x ↔ P i c' x) ∧ (P i x c ↔ P i x c')))

def non_clone_choice_ind_clones : VSCC → Prop := λ F, clones P c D → (∀ a : {x : X // x ≠ c}, a ∉ D → (a.val ∈ (F V X P) ↔ a ∈ (F V {x : X // x ≠ c} (minus_candidate P c))))

def clone_choice_ind_clones : VSCC → Prop := λ F, clones P c D → ((c ∉ (F V X P) ∧ (∀ c' : {x : X // x ≠ c}, c' ∈ D → c'.val ∉ (F V X P))) ↔ (∀ c' ∈ D, c' ∉ (F V {x : X // x ≠ c} (minus_candidate P c))))

lemma margin_eq_margin_minus_candidate [fintype V] {a b : {x : X // x ≠ c}} : margin P a b = margin (minus_candidate P c) a b :=
begin
  obviously,
end

lemma margin_eq_clone_non_clone [fintype V] (b : {x : X // x ≠ c}) (e ∈ D) (p : b ∉ D) : clones P c D → margin P c b = margin (minus_candidate P c) e b :=
begin
  intro clone,
  unfold margin,
  have m1 : ((finset.filter (λ (x_1 : V), P x_1 c ↑b) finset.univ).card) = ((finset.filter (λ (x_1 : V), minus_candidate P c x_1 e b) finset.univ).card),
  apply finset.card_congr _ _ _ _,
  intros a a_spec, exact a,
  intro a, simp, unfold minus_candidate, intro p1,
  unfold clones at clone,
  cases clone with n clone,
  have clone := clone e H b a p,
  exact clone.left.mp p1,
  intros v1 v2 hv1 hv2, simp,
  intros a ha,
  use a,
  simp, simp at ha,
  cases clone with n clone,
  have clone := clone e H b a p,
  exact clone.left.mpr ha,

  have m2 : ((finset.filter (λ (x_1 : V), P x_1 ↑b c) finset.univ).card) = ((finset.filter (λ (x_1 : V), minus_candidate P c x_1 b e) finset.univ).card),
  apply finset.card_congr _ _ _ _,
  intros a a_spec, exact a,
  intro a, simp, unfold minus_candidate, intro p1,
  unfold clones at clone,
  cases clone with n clone,
  have clone := clone e H b a p,
  exact clone.right.mp p1,
  intros v1 v2 hv1 hv2, simp,
  intros a ha,
  use a,
  simp, simp at ha,
  cases clone with n clone,
  have clone := clone e H b a p,
  exact clone.right.mpr ha,

  rw m1, rw m2,
end

lemma margin_eq_clone_non_clone' [fintype V] {b : {x : X // x ≠ c}} {e : {x : X // x ≠ c}} (H : e ∈ D) (p : b ∉ D) : clones P c D → margin P b c = margin (minus_candidate P c) b e :=
begin
  intro clone,
  have x := margin_eq_clone_non_clone P c D b e H p clone,
  rw margin_antisymmetric,
  rw x,
  rw margin_antisymmetric,
  rw int.neg_neg,
end

-- y → d → d' → x
def remove_clones : list X → list X := λ l, to_path (list.map (λ x : X, (ite (∀p : (x ≠ c), (⟨x,p⟩ : {x : X // x ≠ c}) ∈ D) c x)) l)

lemma replace_clones_helper {x : X} (h : ¬∀ (p : x ≠ c), (⟨x, p⟩ : { x : X // x ≠ c}) ∈ D) : x ≠ c :=
begin
  obviously,
end

def replace_clones (d ∈ D) : list X → list {x : X // x ≠ c} := λ l, to_path (list.map (λ x, (dite (∀p : (x ≠ c), (⟨x,p⟩ : {x : X // x ≠ c}) ∈ D) (λ h, d) (λ h, ⟨x, replace_clones_helper c D h⟩)) ) l)

def remove_clones' : list {x : X // x ≠ c} → list X := λ l, to_path (l.map (λ x, (ite (x ∈ D) c x))) 

lemma remove_clones_nil_iff (l : list X) : l = list.nil ↔ remove_clones c D l = list.nil :=
begin
  split,
  intro n,
  rw n,
  unfold remove_clones,
  rw list.map_nil _,
  rw to_path_eq_nil_iff,
  intro n,
  unfold remove_clones at n,
  rw to_path_eq_nil_iff at n,
  rw list.map_eq_nil at n,
  exact n,
end

lemma remove_clones_ne_nil_iff (l : list X) : l ≠ list.nil ↔ remove_clones c D l ≠ list.nil := not_iff_not.mpr (remove_clones_nil_iff c D l)

lemma remove_clones_nodup (l : list X) : (remove_clones c D l).nodup :=
begin
  unfold remove_clones,
  apply to_path_nodup,
end

lemma remove_clones_first_elem (l : list X) (a : X) (e : ∀(p : a ≠ c), (⟨a, p⟩ : {x : X // x ≠ c}) ∉ D) (n : l ≠ list.nil) : ((l.nth_le 0 (list.length_pos_of_ne_nil n)) = a) → (((remove_clones c D l).nth_le 0 (list.length_pos_of_ne_nil ((remove_clones_ne_nil_iff c D l).mp n))) = a) :=
begin
  unfold remove_clones,
  intro m,
  rw to_path_first_elem,
  rw list.nth_le_map _ _ (list.length_pos_of_ne_nil n),
  rw m,
  simp,
  intro p,
  
  apply eq.symm,
  contrapose m,
  exfalso,
  specialize e m,
  specialize p m,
  exact e p,

  intro con,
  rw list.map_eq_nil at con,
  exact n con,
end 

lemma remove_clones_last_elem (l : list X) (a : X) (e : ∀(p : a ≠ c), (⟨a, p⟩ : {x : X // x ≠ c}) ∉ D) (n : l ≠ list.nil) : ((l.last n) = a) → (((remove_clones c D l).last ((remove_clones_ne_nil_iff c D l).mp n)) = a) :=
begin
  unfold remove_clones,
  intro m,
  rw to_path_last_elem,
  rw list.last_map,
  rw m,
  simp,
  intro con,
  apply eq.symm,
  contrapose m,
  exfalso,
  specialize e m,
  specialize con m,
  exact e con,
end

lemma remove_clones'_nil_iff (l : list {x : X // x ≠ c}) : l = list.nil ↔ remove_clones' c D l = list.nil :=
begin
  split,
  intro n,
  rw n,
  unfold remove_clones',
  rw list.map_nil _,
  rw to_path_eq_nil_iff,
  intro n,
  unfold remove_clones' at n,
  rw to_path_eq_nil_iff at n,
  rw list.map_eq_nil at n,
  exact n,
end

lemma remove_clones'_ne_nil_iff (l : list {x : X // x ≠ c}) : l ≠ list.nil ↔ remove_clones' c D l ≠ list.nil := not_iff_not.mpr (remove_clones'_nil_iff c D l)

lemma remove_clones'_nodup (l : list {x : X // x ≠ c}) : (remove_clones' c D l).nodup :=
begin
  unfold remove_clones',
  apply to_path_nodup,
end

lemma remove_clones'_first_elem (l : list {x : X // x ≠ c}) (a : {x : X // x ≠ c}) (e : a ∉ D) (n : l ≠ list.nil) : ((l.nth_le 0 (list.length_pos_of_ne_nil n)) = a) → (((remove_clones' c D l).nth_le 0 (list.length_pos_of_ne_nil ((remove_clones'_ne_nil_iff c D l).mp n))) = a) :=
begin
  unfold remove_clones',
  intro m,
  rw to_path_first_elem,
  rw list.nth_le_map _ _ (list.length_pos_of_ne_nil n),
  rw m,
  simp,
  intro p,
  exfalso,
  exact e p,

  intro con,
  rw list.map_eq_nil at con,
  exact n con,
end 

lemma remove_clones'_last_elem (l : list {x : X // x ≠ c}) (a : {x : X // x ≠ c}) (e : a ∉ D) (n : l ≠ list.nil) : ((l.last n) = a) → (((remove_clones' c D l).last ((remove_clones'_ne_nil_iff c D l).mp n)) = a) :=
begin
  unfold remove_clones',
  intro m,
  rw to_path_last_elem,
  rw list.last_map,
  rw m,
  simp,
  intro con,
  exfalso,
  exact e con,
end

lemma replace_clones_nil_iff (l : list X) {d ∈ D} : l = list.nil ↔ replace_clones c D d H l = list.nil :=
begin
  split,
  intro n,
  rw n,
  unfold replace_clones,
  rw list.map_nil _,
  rw to_path_eq_nil_iff,
  intro n,
  unfold replace_clones at n,
  rw to_path_eq_nil_iff at n,
  rw list.map_eq_nil at n,
  exact n,
end

lemma replace_clones_ne_nil_iff (d ∈ D) (l : list X) : l ≠ list.nil ↔ replace_clones c D d H l ≠ list.nil := not_iff_not.mpr (replace_clones_nil_iff c D l)

lemma replace_clones_nodup (l : list X) {d ∈ D} : (replace_clones c D d H l).nodup :=
begin
  unfold replace_clones,
  apply to_path_nodup,
end

lemma replace_clones_first_elem (l : list X) (a : X) (e : ¬ ∀(p : a ≠ c), (⟨a, p⟩ : {x : X // x ≠ c}) ∈ D) (n : l ≠ list.nil) {d ∈ D} : ((l.nth_le 0 (list.length_pos_of_ne_nil n)) = a) → (((replace_clones c D d H l).nth_le 0 (list.length_pos_of_ne_nil ((replace_clones_ne_nil_iff c D d H l).mp n))) = ⟨a, replace_clones_helper c D e⟩) :=
begin
  unfold replace_clones,
  intro m,
  rw to_path_first_elem,
  rw list.nth_le_map _ _ (list.length_pos_of_ne_nil n),
  rw m,
  split_ifs,
  refl,
  
  apply (not_iff_not.mpr list.map_eq_nil).mpr,
  exact n,
end 

lemma replace_clones_last_elem (l : list X) (a : X) (e : ¬∀(p : a ≠ c), (⟨a, p⟩ : {x : X // x ≠ c}) ∈ D) (n : l ≠ list.nil) {d ∈ D} : ((l.last n) = a) → (((replace_clones c D d H l).last ((replace_clones_ne_nil_iff c D d H l).mp n)) = ⟨a, replace_clones_helper c D e⟩) :=
begin
  unfold replace_clones,
  intro m,
  rw to_path_last_elem,
  rw list.last_map,
  rw m,
  split_ifs,
  refl,
end

lemma replace_clones_last_c (l : list X) (n : l ≠ list.nil) {d ∈ D} : ((l.last n) = c) → (((replace_clones c D d H l).last ((replace_clones_ne_nil_iff c D d H l).mp n)) = d) :=
begin
  unfold replace_clones,
  intro m,
  rw to_path_last_elem,
  rw list.last_map,
  rw m,
  split_ifs,
  refl,
  push_neg at h,
  cases h with contr h,
  exfalso,
  exact false_of_ne contr,
end

lemma remove_clones_chain'_of_chain' [fintype V] (l : list X) (b : {x : X // x ≠ c}) (e : b ∉ D) (d ∈ D) (clone : clones P c D) : 
  list.chain' (λ (a b_1 : X), margin P ↑d ↑b ≤ margin P a b_1) l → list.chain' (λ (a b_1 : X), margin P c ↑b ≤ margin P a b_1) (remove_clones c D l) :=
begin
  intro a,
  induction l,
   {obviously,},
  unfold remove_clones,
  simp [to_path],
  specialize l_ih (and.right (list.chain'_cons'.mp a)),
  by_cases (list.index_of (ite (∀ (h : ¬l_hd = c), (⟨l_hd, h⟩ : {x : X // x ≠ c}) ∈ D) c l_hd) (to_path (list.map (λ (x : X), ite (∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D) c x) l_tl)) < (to_path (list.map (λ (x : X), ite (∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D) c x) l_tl)).length),
  simp_rw (ite_left_if h),
  exact drop_chain'_of_chain' l_ih,

  simp_rw (ite_right_if h),
  by_cases j : l_tl = list.nil,
  rw j,
  rw list.map_nil,
  rw ←j,
  rw (to_path_eq_nil_iff l_tl).mpr j,
  exact list.chain'_singleton (ite (∀ (h : ¬l_hd = c), (⟨l_hd, _⟩ : {x : X // x ≠ c}) ∈ D) c l_hd),

  rw list.chain'_iff_nth_le,
  rw list.chain'_iff_nth_le at l_ih,
  rw list.chain'_iff_nth_le at a,
  intros i i_bounds,
  have nodup := h,
  by_cases i = 0,
  have i_eq := h,
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
  rw to_path_first_elem',
  simp,
  
  by_cases (∀ (h : ¬l_hd = c), (⟨l_hd, h⟩ : {x : X // x ≠ c}) ∈ D),
  rw ite_left_if h,
  have h' := h,
  by_cases (∀ (h_1 : ¬l_tl.nth_le 0 (list.length_pos_of_ne_nil j) = c), (⟨l_tl.nth_le 0 (list.length_pos_of_ne_nil j), h_1⟩ : {x : X // x ≠ c}) ∈ D),
  exfalso,
  contrapose nodup,
  push_neg,
  rw list.index_of_lt_length,
  rw ite_left_if h',
  rw list.mem_iff_nth_le,
  use 0,
  have len : 0 < (to_path (list.map (λ (x : X), ite (∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D) c x) l_tl)).length,
  change (0 < (remove_clones c D l_tl).length),
  apply list.length_pos_of_ne_nil,
  rw ←remove_clones_ne_nil_iff,
  exact j,
  use len,
  rw to_path_first_elem',
  rw list.nth_le_map (λ (x : X), ite (∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D) c x) _ (list.length_pos_of_ne_nil j),
  simp,
  intro w,
  specialize h w,
  intro contr,
  exfalso, exact contr h,

  rw ite_right_if h,
  push_neg at h,
  cases h with not_c not_d,
  by_cases l_hd = c,
  rw h at a,
  rw margin_eq_clone_non_clone P c D b d H e clone,
  rw ←margin_eq_margin_minus_candidate,
  exact a,

  specialize h' h,
  rw margin_eq_clone_non_clone P c D b d H e clone,
  have r := margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ ⟨l_hd, h⟩ h' not_d clone,
  simp at r,
  rw r,
  rw ←margin_eq_margin_minus_candidate, rw ←margin_eq_margin_minus_candidate,
  exact a,

  rw ite_right_if h,
  have h' := h,
  by_cases (∀ (h_1 : ¬l_tl.nth_le 0 (list.length_pos_of_ne_nil j) = c), (⟨l_tl.nth_le 0 (list.length_pos_of_ne_nil j), h_1⟩ : {x : X // x ≠ c}) ∈ D),
  rw ite_left_if h,
  push_neg at h',
  cases h' with not_c not_d,
  have h'' := h,
  by_cases (l_tl.nth_le 0 (list.nth_le._main._proof_1 l_hd l_tl 0 (nat.lt_pred_iff.mp a_proof))) = c,
  rw h at a,
  rw margin_eq_clone_non_clone P c D b d H e clone,
  rw ←margin_eq_margin_minus_candidate,
  exact a,

  specialize h'' h,
  rw margin_eq_clone_non_clone P c D b d H e clone,
  have r := margin_eq_clone_non_clone' P c D h'' not_d clone,
  simp at r,
  rw r,
  rw ←margin_eq_margin_minus_candidate, rw ←margin_eq_margin_minus_candidate,
  exact a,

  rw ite_right_if h,
  rw margin_eq_clone_non_clone P c D b d H e clone,
  exact a,

  rw [list.nth_le],
  specialize l_ih (i - 1),
  rw list.length_cons at i_bounds,
  simp only [nat.add_succ_sub_one, add_zero] at i_bounds,
  have o : ∀ i n, ¬ i = 0 → i < n → i - 1 < n - 1 := by omega,
  specialize l_ih (o i (to_path (list.map (λ (x : X), ite (∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D) c x) l_tl)).length h i_bounds),
  --change (margin P c ↑b ≤ margin P ((((ite (∀ (h : ¬l_hd = c), (⟨l_hd, h⟩ : {x : X // x ≠ c}) ∈ D) c l_hd)) :: (remove_clones c D l_tl)).nth_le i (nat.lt_of_lt_pred i_bounds)) ((remove_clones c D l_tl).nth_le i _)),
  rw nth_le_cons h,
  have o : ∀ i, ¬ i = 0 → i - 1 + 1 = i := by omega,
  simp_rw (o i h) at l_ih,
  exact l_ih,
end

lemma nodup_lift_of_nodup {l : list {x : X // x ≠ c}} : l.nodup → (lift l : list X).nodup :=
begin
  intro n,
  unfold lift,
  unfold has_lift.lift,
  rw list.nodup_map_iff_inj_on,
  obviously,
end

lemma lift_ne_nil_iff {l : list {x : X // x ≠ c}} : (lift l : list X) ≠ list.nil ↔ l ≠ list.nil:=
begin
  unfold lift, unfold has_lift.lift, change (¬ list.map coe l = list.nil ↔ l ≠ list.nil),
   rw list.map_eq_nil,
end

lemma dite_left_if {p : Prop} {α : Type} [decidable p] {a : p → α} {b : ¬ p → α} (proof : p) : dite p a b = a proof := 
begin
  split_ifs, refl,
end

lemma dite_right_if {p : Prop} {α : Type} [decidable p] {a : p → α} {b : ¬ p → α} (proof : ¬p) : ¬ p → dite p a b = b proof :=
begin
  split_ifs, intro unused, refl,
end

--set_option pp.all true 

lemma A6_chain [fintype V] (l : list X) {b : {x : X // x ≠ c}} {d : {x : X // x ≠ c}} {d' : {x : X // x ≠ c}} (H : d ∈ D) (clone : clones P c D) : list.chain' (λ (a b_1 : X), margin P ↑b ↑d' ≤ margin P a b_1) l
→ list.chain' (λ (a b_1 : {x // x ≠ c}), margin (minus_candidate P c) b d' ≤ margin (minus_candidate P c) a b_1) (replace_clones c D d H l) :=
begin
  intro a,
  induction l,
    {obviously,},
  unfold replace_clones,
  simp [to_path],
  specialize l_ih (and.right (list.chain'_cons'.mp a)),
  by_cases @has_lt.lt.{0} nat nat.has_lt
  (@list.index_of.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
     (λ (a b : @subtype.{1} X (λ (x : X), @ne.{1} X x c)),
        classical.prop_decidable (@eq.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) a b))
     (@dite.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
        (∀ (h : not (@eq.{1} X l_hd c)),
           @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
             (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
             (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
             (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                   (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                      (iff.refl (@ne.{1} X l_hd c))
                      (not (@eq.{1} X l_hd c))
                      (@ne.def.{1} X l_hd c))
                   h))
             D)
        (@forall_prop_decidable (not (@eq.{1} X l_hd c))
           (λ (h : not (@eq.{1} X l_hd c)),
              @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                   (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                      (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                         (iff.refl (@ne.{1} X l_hd c))
                         (not (@eq.{1} X l_hd c))
                         (@ne.def.{1} X l_hd c))
                      h))
                D)
           (@ne.decidable.{1} X (λ (a b : X), classical.prop_decidable (@eq.{1} X a b)) l_hd c)
           (λ (h : not (@eq.{1} X l_hd c)),
              @set.decidable_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) D
                (λ (a : @subtype.{1} X (λ (x : X), @ne.{1} X x c)), classical.prop_decidable (D a))
                (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                   (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                      (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                         (iff.refl (@ne.{1} X l_hd c))
                         (not (@eq.{1} X l_hd c))
                         (@ne.def.{1} X l_hd c))
                      h))))
        (λ
         (h :
           ∀ (h : not (@eq.{1} X l_hd c)),
             @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
               (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
               (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
               (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                  (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                     (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                        (iff.refl (@ne.{1} X l_hd c))
                        (not (@eq.{1} X l_hd c))
                        (@ne.def.{1} X l_hd c))
                     h))
               D), d)
        (λ
         (h :
           not
             (∀ (h : not (@eq.{1} X l_hd c)),
                @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                  (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                  (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                  (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                     (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                        (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                           (iff.refl (@ne.{1} X l_hd c))
                           (not (@eq.{1} X l_hd c))
                           (@ne.def.{1} X l_hd c))
                        h))
                  D)),
           @subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
             (@replace_clones_helper X c D l_hd
                (@iff.mpr
                   (not
                      (∀ (p : @ne.{1} X l_hd c),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd p)
                           D))
                   (not
                      (∀ (h : not (@eq.{1} X l_hd c)),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                              (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                                    (iff.refl (@ne.{1} X l_hd c))
                                    (not (@eq.{1} X l_hd c))
                                    (@ne.def.{1} X l_hd c))
                                 h))
                           D))
                   (@not_iff_not_of_iff
                      (∀ (p : @ne.{1} X l_hd c),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd p)
                           D)
                      (∀ (h : not (@eq.{1} X l_hd c)),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                              (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                                    (iff.refl (@ne.{1} X l_hd c))
                                    (not (@eq.{1} X l_hd c))
                                    (@ne.def.{1} X l_hd c))
                                 h))
                           D)
                      (@forall_prop_congr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                         (λ (h : @ne.{1} X l_hd c),
                            @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                              (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd h)
                              D)
                         (λ (h : @ne.{1} X l_hd c),
                            @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                              (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd h)
                              D)
                         (λ (h : @ne.{1} X l_hd c),
                            iff.refl
                              (@has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                 (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                 (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                 (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd h)
                                 D))
                         (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                            (iff.refl (@ne.{1} X l_hd c))
                            (not (@eq.{1} X l_hd c))
                            (@ne.def.{1} X l_hd c))))
                   h))))
     (@to_path (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
        (@list.map.{0 0} X (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
           (λ (x : X),
              @dite.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                (∀ (h : not (@eq.{1} X x c)),
                   @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                     (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                        (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                           (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                              (iff.refl (@ne.{1} X x c))
                              (not (@eq.{1} X x c))
                              (@ne.def.{1} X x c))
                           h))
                     D)
                (@forall_prop_decidable (not (@eq.{1} X x c))
                   (λ (h : not (@eq.{1} X x c)),
                      @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                        (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))
                        D)
                   (@ne.decidable.{1} X (λ (a b : X), classical.prop_decidable (@eq.{1} X a b)) x c)
                   (λ (h : not (@eq.{1} X x c)),
                      @set.decidable_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) D
                        (λ (a : @subtype.{1} X (λ (x : X), @ne.{1} X x c)), classical.prop_decidable (D a))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))))
                (λ
                 (h :
                   ∀ (h : not (@eq.{1} X x c)),
                     @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                       (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                          (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                             (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                (iff.refl (@ne.{1} X x c))
                                (not (@eq.{1} X x c))
                                (@ne.def.{1} X x c))
                             h))
                       D), d)
                (λ
                 (h :
                   not
                     (∀ (h : not (@eq.{1} X x c)),
                        @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                          (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                             (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                   (iff.refl (@ne.{1} X x c))
                                   (not (@eq.{1} X x c))
                                   (@ne.def.{1} X x c))
                                h))
                          D)),
                   @subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                     (@replace_clones_helper X c D x
                        (@iff.mpr
                           (not
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D))
                           (not
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D))
                           (@not_iff_not_of_iff
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D)
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D)
                              (@forall_prop_congr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    iff.refl
                                      (@has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                         (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                         D))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                    (iff.refl (@ne.{1} X x c))
                                    (not (@eq.{1} X x c))
                                    (@ne.def.{1} X x c))))
                           h))))
           l_tl)))
  (@list.length.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
     (@to_path (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
        (@list.map.{0 0} X (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
           (λ (x : X),
              @dite.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                (∀ (h : not (@eq.{1} X x c)),
                   @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                     (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                        (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                           (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                              (iff.refl (@ne.{1} X x c))
                              (not (@eq.{1} X x c))
                              (@ne.def.{1} X x c))
                           h))
                     D)
                (@forall_prop_decidable (not (@eq.{1} X x c))
                   (λ (h : not (@eq.{1} X x c)),
                      @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                        (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))
                        D)
                   (@ne.decidable.{1} X (λ (a b : X), classical.prop_decidable (@eq.{1} X a b)) x c)
                   (λ (h : not (@eq.{1} X x c)),
                      @set.decidable_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) D
                        (λ (a : @subtype.{1} X (λ (x : X), @ne.{1} X x c)), classical.prop_decidable (D a))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))))
                (λ
                 (h :
                   ∀ (h : not (@eq.{1} X x c)),
                     @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                       (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                          (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                             (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                (iff.refl (@ne.{1} X x c))
                                (not (@eq.{1} X x c))
                                (@ne.def.{1} X x c))
                             h))
                       D), d)
                (λ
                 (h :
                   not
                     (∀ (h : not (@eq.{1} X x c)),
                        @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                          (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                             (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                   (iff.refl (@ne.{1} X x c))
                                   (not (@eq.{1} X x c))
                                   (@ne.def.{1} X x c))
                                h))
                          D)),
                   @subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                     (@replace_clones_helper X c D x
                        (@iff.mpr
                           (not
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D))
                           (not
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D))
                           (@not_iff_not_of_iff
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D)
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D)
                              (@forall_prop_congr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    iff.refl
                                      (@has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                         (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                         D))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                    (iff.refl (@ne.{1} X x c))
                                    (not (@eq.{1} X x c))
                                    (@ne.def.{1} X x c))))
                           h))))
           l_tl))),

  simp_rw (ite_left_if h),
  exact drop_chain'_of_chain' l_ih,

  simp_rw (ite_right_if h),
  by_cases j : l_tl = list.nil,
  rw j,
  simp [to_path],
  
  rw list.chain'_iff_nth_le,
  rw list.chain'_iff_nth_le at l_ih,
  rw list.chain'_iff_nth_le at a,
  intros i i_bounds,
  rename h nodup,
  by_cases i = 0,
  rename h i_eq,
  simp_rw i_eq,
  rw [list.nth_le], rw [list.nth_le],
  specialize a 0,
  have a_proof : 0 < (l_hd :: l_tl).length - 1,
  rw list.length_cons,
  simp only [nat.add_succ_sub_one, add_zero],
  exact (list.length_pos_of_ne_nil j),
  specialize a a_proof,
  rw [list.nth_le] at a, rw [list.nth_le] at a,
  have x := (to_path_first_elem X l_tl j),
  rw to_path_first_elem',
  simp,
  
  split_ifs with h',
  by_cases (∀ (h_1 : ¬l_tl.nth_le 0 (list.length_pos_of_ne_nil j) = c), (⟨l_tl.nth_le 0 (list.length_pos_of_ne_nil j), h_1⟩ : {x : X // x ≠ c}) ∈ D),
  exfalso,
  contrapose nodup,
  push_neg,
  rw list.index_of_lt_length,
  rw dite_left_if h',
  rw list.mem_iff_nth_le,
  use 0,
  have len : (0 < (replace_clones c D d H l_tl).length),
  apply list.length_pos_of_ne_nil,
  rw ←replace_clones_ne_nil_iff,
  exact j,
  use len,
  rw to_path_first_elem',
  rw list.nth_le_map (λ (x : X), dite (∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D) (λ (h : ∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D), d) (λ (h : ¬∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D), ⟨x, replace_clones_helper c D h⟩)) _ (list.length_pos_of_ne_nil j),
  simp,
  rw dite_left_if h,

  rw dite_right_if h,

  push_neg at h,
  cases h with not_c not_d,
  by_cases l_hd = c,
  rw h at a,
  rw ←margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ d H not_d clone,
  rw ←margin_eq_margin_minus_candidate,
  exact a,


  specialize h' h,
  rw ←margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ d H not_d clone,
  rw margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ ⟨l_hd, h⟩ h' not_d clone,
  rw ←margin_eq_margin_minus_candidate, rw ←margin_eq_margin_minus_candidate,
  exact a,
  exact h,

  by_cases (∀ (h_1 : ¬l_tl.nth_le 0 (list.length_pos_of_ne_nil j) = c), (⟨l_tl.nth_le 0 (list.length_pos_of_ne_nil j), h_1⟩ : {x : X // x ≠ c}) ∈ D),
  rw dite_left_if h,
  push_neg at h',
  cases h' with not_c not_d,
  rename h h'',
  by_cases (l_tl.nth_le 0 (list.nth_le._main._proof_1 l_hd l_tl 0 (nat.lt_pred_iff.mp a_proof))) = c,
  rw h at a,
  rw ←margin_eq_clone_non_clone' P c D H not_d clone,
  rw ←margin_eq_margin_minus_candidate,
  exact a,

  specialize h'' h,
  rw ←margin_eq_clone_non_clone' P c D H not_d clone,
  rw margin_eq_clone_non_clone' P c D h'' not_d clone,
  rw ←margin_eq_margin_minus_candidate, rw ←margin_eq_margin_minus_candidate,
  exact a,

  rw dite_right_if h,
  rw ←margin_eq_margin_minus_candidate, rw ←margin_eq_margin_minus_candidate,
  exact a,
  exact h,

  rw [list.nth_le],
  specialize l_ih (i - 1),
  rw list.length_cons at i_bounds,
  simp only [nat.add_succ_sub_one, add_zero] at i_bounds,
  have o : ∀ i n, ¬ i = 0 → i < n → i - 1 < n - 1 := by omega,
  specialize l_ih (o i (replace_clones c D d H l_tl).length h i_bounds),
  rw nth_le_cons h,
  have o : ∀ i, ¬ i = 0 → i - 1 + 1 = i := by omega,
  simp_rw (o i h) at l_ih,
  exact l_ih,
end

-- A.5 might not be true if a and b are in D?
lemma clone_maintains_defeat (a b : {x : X // x ≠ c}) (H : b ∉ D) : clones P c D → ((split_cycle_VCCR V {x : X // x ≠ c} (minus_candidate P c)) a b ↔ (split_cycle_VCCR V X P) a b) :=
begin
  intro clone,
  rw split_cycle_definitions,
  unfold split_cycle_VCCR',
  simp,
  split,
  intro f,
  introI fV,
  cases f with m f,
  rw margin_eq_margin_minus_candidate,
  use m,
  intros l n ne_nil b_mem a_mem,
  have clone' := clone,
  unfold clones at clone,
  cases clone with n clone,
  let d := (ite (a ∈ D) a n.some),
  have d_spec : d ∈ D,
    {change (ite (a ∈ D) a n.some) ∈ D, split_ifs, exact h, exact n.some_spec, },
  specialize f (replace_clones c D d d_spec l),
  specialize f (replace_clones_nodup c D l),
  specialize f ((replace_clones_ne_nil_iff c D d d_spec l).mp ne_nil),
  have b_not : ¬∀ (p : ↑b ≠ c), (⟨↑b, p⟩ : {x : X // x ≠ c}) ∈ D,
   {push_neg, use b.property, simp, exact H,},
  rw (replace_clones_first_elem c D l b b_not ne_nil b_mem) at f,
  simp at f,
  have last_elem : (replace_clones c D d d_spec l).last ((replace_clones_ne_nil_iff c D d d_spec l).mp ne_nil) = a,
    {change (replace_clones c D (ite (a ∈ D) a n.some) d_spec l).last ((replace_clones_ne_nil_iff c D d d_spec l).mp ne_nil) = a,
    split_ifs, unfold replace_clones, rw to_path_last_elem, rw list.last_map, split_ifs, 
    refl, push_neg at h_1, simp_rw a_mem, simp, exact ne_nil, rw replace_clones_last_elem c D l _ _ ne_nil a_mem, simp, 
    push_neg, use a.property, simp, exact h, },
  specialize f last_elem,
  contrapose f,
  push_neg at f, push_neg, 
  exact A6_chain P c D l d_spec clone' f,


  intro f,
  introI fV,
  cases f with m f,
  rw ←margin_eq_margin_minus_candidate,
  use m,
  intros l l_nodup ne_nil b_mem a_mem,
  specialize f ↑l,
  contrapose f,
  push_neg,
  split,
  exact nodup_lift_of_nodup c l_nodup,
  use (lift_ne_nil_iff c).mpr ne_nil,
  unfold coe, unfold lift_t, unfold has_lift_t.lift,
  unfold lift, unfold has_lift.lift, unfold coe_t, 
  unfold has_coe_t.coe, unfold coe_b, unfold has_coe.coe,
  split,
  rw list.nth_le_map, rw b_mem, refl,
  split, 
  have test := list.last_map (coe : {x // x ≠ c} → X) ne_nil,
  rw a_mem at test,
  change (list.map coe l).last _ = ↑a,
  rw ←test,
  refl,
  push_neg at f,
  apply (list.chain'_map (coe : {x // x ≠ c} → X)).mpr,
  refine list.chain'.imp _ f,
  intros a_1 b_1 m_1,
  rw ←margin_eq_margin_minus_candidate at m_1,
  exact m_1,
end

lemma clone_maintains_defeat' (a b : {x : X // x ≠ c}) (H : a ∉ D) (H' : b ∈ D) : clones P c D → ((split_cycle_VCCR V {x : X // x ≠ c} (minus_candidate P c)) a b ↔ (split_cycle_VCCR V X P) a b) :=
begin
  intro clone,
  rw split_cycle_definitions,
  unfold split_cycle_VCCR',
  simp,
  split,
  intro f,
  introI fV,
  cases f with m f,
  rw margin_eq_margin_minus_candidate,
  use m,
  intros l n ne_nil b_mem a_mem,
  have clone' := clone,
  unfold clones at clone,
  cases clone with n clone,
  let d := b,
  let d_spec := H',
  specialize f (replace_clones c D d d_spec l),
  specialize f (replace_clones_nodup c D l),
  specialize f ((replace_clones_ne_nil_iff c D d d_spec l).mp ne_nil),
  have b_not : ¬∀ (p : ↑a ≠ c), (⟨↑a, p⟩ : {x : X // x ≠ c}) ∈ D,
   {push_neg, use a.property, simp, exact H,},

  contrapose f, push_neg, push_neg at f,
  split,
  unfold replace_clones,
  rw to_path_first_elem',
  rw list.nth_le_map,
  split_ifs,
  refl,
  simp_rw b_mem, 
  simp,
  exact list.length_pos_of_ne_nil ne_nil,
  split,
  rw (replace_clones_last_elem c D l a b_not ne_nil a_mem),
  simp,
  exact A6_chain P c D l d_spec clone' f,


  intro f,
  introI fV,
  cases f with m f,
  rw ←margin_eq_margin_minus_candidate,
  use m,
  intros l l_nodup ne_nil b_mem a_mem,
  specialize f ↑l,
  contrapose f,
  push_neg at f,
  push_neg,
  split,
  exact nodup_lift_of_nodup c l_nodup,
  use (lift_ne_nil_iff c).mpr ne_nil,
  unfold coe, unfold lift_t, unfold has_lift_t.lift,
  unfold lift, unfold has_lift.lift, unfold coe_t, 
  unfold has_coe_t.coe, unfold coe_b, unfold has_coe.coe,
  split,
  rw list.nth_le_map, rw b_mem, refl,
  split, 
  have test := list.last_map (coe : {x // x ≠ c} → X) ne_nil,
  rw a_mem at test,
  change (list.map coe l).last _ = ↑a,
  rw ←test,
  refl,
  apply (list.chain'_map (coe : {x // x ≠ c} → X)).mpr,
  refine list.chain'.imp _ f,
  intros a_1 b_1 m_1,
  rw ←margin_eq_margin_minus_candidate at m_1,
  exact m_1,
end

lemma A5_chain {l : list X} [fintype V] {d : {x : X // x ≠ c}} {b : {x : X // x ≠ c}} (H : d ∈ D) (H' : b ∉ D) (clone : clones P c D) : list.chain' (λ (a b_1 : X), margin P c ↑b ≤ margin P a b_1) l → list.chain' (λ (a b_1 : {x // x ≠ c}), margin P ↑d ↑b ≤ margin P ↑a ↑b_1) (replace_clones c D d H l) :=
begin
  intro a,
  induction l,
    {obviously,},
  unfold replace_clones,
  simp [to_path],
  specialize l_ih (and.right (list.chain'_cons'.mp a)),
  by_cases @has_lt.lt.{0} nat nat.has_lt
  (@list.index_of.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
     (λ (a b : @subtype.{1} X (λ (x : X), @ne.{1} X x c)),
        classical.prop_decidable (@eq.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) a b))
     (@dite.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
        (∀ (h : not (@eq.{1} X l_hd c)),
           @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
             (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
             (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
             (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                   (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                      (iff.refl (@ne.{1} X l_hd c))
                      (not (@eq.{1} X l_hd c))
                      (@ne.def.{1} X l_hd c))
                   h))
             D)
        (@forall_prop_decidable (not (@eq.{1} X l_hd c))
           (λ (h : not (@eq.{1} X l_hd c)),
              @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                   (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                      (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                         (iff.refl (@ne.{1} X l_hd c))
                         (not (@eq.{1} X l_hd c))
                         (@ne.def.{1} X l_hd c))
                      h))
                D)
           (@ne.decidable.{1} X (λ (a b : X), classical.prop_decidable (@eq.{1} X a b)) l_hd c)
           (λ (h : not (@eq.{1} X l_hd c)),
              @set.decidable_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) D
                (λ (a : @subtype.{1} X (λ (x : X), @ne.{1} X x c)), classical.prop_decidable (D a))
                (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                   (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                      (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                         (iff.refl (@ne.{1} X l_hd c))
                         (not (@eq.{1} X l_hd c))
                         (@ne.def.{1} X l_hd c))
                      h))))
        (λ
         (h :
           ∀ (h : not (@eq.{1} X l_hd c)),
             @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
               (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
               (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
               (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                  (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                     (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                        (iff.refl (@ne.{1} X l_hd c))
                        (not (@eq.{1} X l_hd c))
                        (@ne.def.{1} X l_hd c))
                     h))
               D), d)
        (λ
         (h :
           not
             (∀ (h : not (@eq.{1} X l_hd c)),
                @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                  (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                  (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                  (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                     (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                        (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                           (iff.refl (@ne.{1} X l_hd c))
                           (not (@eq.{1} X l_hd c))
                           (@ne.def.{1} X l_hd c))
                        h))
                  D)),
           @subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
             (@replace_clones_helper X c D l_hd
                (@iff.mpr
                   (not
                      (∀ (p : @ne.{1} X l_hd c),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd p)
                           D))
                   (not
                      (∀ (h : not (@eq.{1} X l_hd c)),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                              (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                                    (iff.refl (@ne.{1} X l_hd c))
                                    (not (@eq.{1} X l_hd c))
                                    (@ne.def.{1} X l_hd c))
                                 h))
                           D))
                   (@not_iff_not_of_iff
                      (∀ (p : @ne.{1} X l_hd c),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd p)
                           D)
                      (∀ (h : not (@eq.{1} X l_hd c)),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                              (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                                    (iff.refl (@ne.{1} X l_hd c))
                                    (not (@eq.{1} X l_hd c))
                                    (@ne.def.{1} X l_hd c))
                                 h))
                           D)
                      (@forall_prop_congr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                         (λ (h : @ne.{1} X l_hd c),
                            @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                              (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd h)
                              D)
                         (λ (h : @ne.{1} X l_hd c),
                            @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                              (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd h)
                              D)
                         (λ (h : @ne.{1} X l_hd c),
                            iff.refl
                              (@has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                 (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                 (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                 (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd h)
                                 D))
                         (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                            (iff.refl (@ne.{1} X l_hd c))
                            (not (@eq.{1} X l_hd c))
                            (@ne.def.{1} X l_hd c))))
                   h))))
     (@to_path (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
        (@list.map.{0 0} X (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
           (λ (x : X),
              @dite.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                (∀ (h : not (@eq.{1} X x c)),
                   @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                     (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                        (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                           (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                              (iff.refl (@ne.{1} X x c))
                              (not (@eq.{1} X x c))
                              (@ne.def.{1} X x c))
                           h))
                     D)
                (@forall_prop_decidable (not (@eq.{1} X x c))
                   (λ (h : not (@eq.{1} X x c)),
                      @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                        (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))
                        D)
                   (@ne.decidable.{1} X (λ (a b : X), classical.prop_decidable (@eq.{1} X a b)) x c)
                   (λ (h : not (@eq.{1} X x c)),
                      @set.decidable_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) D
                        (λ (a : @subtype.{1} X (λ (x : X), @ne.{1} X x c)), classical.prop_decidable (D a))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))))
                (λ
                 (h :
                   ∀ (h : not (@eq.{1} X x c)),
                     @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                       (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                          (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                             (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                (iff.refl (@ne.{1} X x c))
                                (not (@eq.{1} X x c))
                                (@ne.def.{1} X x c))
                             h))
                       D), d)
                (λ
                 (h :
                   not
                     (∀ (h : not (@eq.{1} X x c)),
                        @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                          (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                             (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                   (iff.refl (@ne.{1} X x c))
                                   (not (@eq.{1} X x c))
                                   (@ne.def.{1} X x c))
                                h))
                          D)),
                   @subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                     (@replace_clones_helper X c D x
                        (@iff.mpr
                           (not
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D))
                           (not
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D))
                           (@not_iff_not_of_iff
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D)
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D)
                              (@forall_prop_congr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    iff.refl
                                      (@has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                         (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                         D))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                    (iff.refl (@ne.{1} X x c))
                                    (not (@eq.{1} X x c))
                                    (@ne.def.{1} X x c))))
                           h))))
           l_tl)))
  (@list.length.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
     (@to_path (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
        (@list.map.{0 0} X (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
           (λ (x : X),
              @dite.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                (∀ (h : not (@eq.{1} X x c)),
                   @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                     (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                        (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                           (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                              (iff.refl (@ne.{1} X x c))
                              (not (@eq.{1} X x c))
                              (@ne.def.{1} X x c))
                           h))
                     D)
                (@forall_prop_decidable (not (@eq.{1} X x c))
                   (λ (h : not (@eq.{1} X x c)),
                      @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                        (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))
                        D)
                   (@ne.decidable.{1} X (λ (a b : X), classical.prop_decidable (@eq.{1} X a b)) x c)
                   (λ (h : not (@eq.{1} X x c)),
                      @set.decidable_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) D
                        (λ (a : @subtype.{1} X (λ (x : X), @ne.{1} X x c)), classical.prop_decidable (D a))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))))
                (λ
                 (h :
                   ∀ (h : not (@eq.{1} X x c)),
                     @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                       (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                          (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                             (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                (iff.refl (@ne.{1} X x c))
                                (not (@eq.{1} X x c))
                                (@ne.def.{1} X x c))
                             h))
                       D), d)
                (λ
                 (h :
                   not
                     (∀ (h : not (@eq.{1} X x c)),
                        @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                          (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                             (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                   (iff.refl (@ne.{1} X x c))
                                   (not (@eq.{1} X x c))
                                   (@ne.def.{1} X x c))
                                h))
                          D)),
                   @subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                     (@replace_clones_helper X c D x
                        (@iff.mpr
                           (not
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D))
                           (not
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D))
                           (@not_iff_not_of_iff
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D)
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D)
                              (@forall_prop_congr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    iff.refl
                                      (@has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                         (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                         D))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                    (iff.refl (@ne.{1} X x c))
                                    (not (@eq.{1} X x c))
                                    (@ne.def.{1} X x c))))
                           h))))
           l_tl))),

  simp_rw (ite_left_if h),
  exact drop_chain'_of_chain' l_ih,

  simp_rw (ite_right_if h),
  by_cases j : l_tl = list.nil,
  rw j,
  simp [to_path],
  
  rw list.chain'_iff_nth_le,
  rw list.chain'_iff_nth_le at l_ih,
  rw list.chain'_iff_nth_le at a,
  intros i i_bounds,
  rename h nodup,
  by_cases i = 0,
  rename h i_eq,
  simp_rw i_eq,
  rw [list.nth_le], rw [list.nth_le],
  specialize a 0,
  have a_proof : 0 < (l_hd :: l_tl).length - 1,
  rw list.length_cons,
  simp only [nat.add_succ_sub_one, add_zero],
  exact (list.length_pos_of_ne_nil j),
  specialize a a_proof,
  rw [list.nth_le] at a, rw [list.nth_le] at a,
  have x := (to_path_first_elem X l_tl j),
  rw to_path_first_elem',
  simp,
  
  split_ifs with h',
  by_cases (∀ (h_1 : ¬l_tl.nth_le 0 (list.length_pos_of_ne_nil j) = c), (⟨l_tl.nth_le 0 (list.length_pos_of_ne_nil j), h_1⟩ : {x : X // x ≠ c}) ∈ D),
  exfalso,
  contrapose nodup,
  push_neg,
  rw list.index_of_lt_length,
  rw dite_left_if h',
  rw list.mem_iff_nth_le,
  use 0,
  have len : (0 < (replace_clones c D d H l_tl).length),
  apply list.length_pos_of_ne_nil,
  rw ←replace_clones_ne_nil_iff,
  exact j,
  use len,
  rw to_path_first_elem',
  rw list.nth_le_map (λ (x : X), dite (∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D) (λ (h : ∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D), d) (λ (h : ¬∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D), ⟨x, replace_clones_helper c D h⟩)) _ (list.length_pos_of_ne_nil j),
  simp,
  rw dite_left_if h,

  rw dite_right_if h,

  push_neg at h,
  cases h with not_c not_d,
  by_cases l_hd = c,
  rw h at a, simp,
  have test := @margin_eq_margin_minus_candidate V X P c _inst_1 d ⟨(l_tl.nth_le 0 _), not_c⟩,
  simp at test,
  rw margin_eq_margin_minus_candidate,
  rw test,
  rw ←margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ d H not_d clone,
  simp,
  rw ←margin_eq_clone_non_clone P c D b d H H' clone,
  exact a,


  specialize h' h,
  simp,
  have test := @margin_eq_margin_minus_candidate V X P c _inst_1 d ⟨(l_tl.nth_le 0 _), not_c⟩,
  simp at test,
  rw margin_eq_margin_minus_candidate,
  rw test,
  rw ←margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ d H not_d clone,
  rw margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ ⟨l_hd, h⟩ h' not_d clone,
  rw ←margin_eq_clone_non_clone P c D b d H H' clone,
  rw ←margin_eq_margin_minus_candidate, 
  simp,
  exact a,
  exact h,

  by_cases (∀ (h_1 : ¬l_tl.nth_le 0 (list.length_pos_of_ne_nil j) = c), (⟨l_tl.nth_le 0 (list.length_pos_of_ne_nil j), h_1⟩ : {x : X // x ≠ c}) ∈ D),
  rw dite_left_if h,
  push_neg at h',
  cases h' with not_c not_d,
  rename h h'',
  by_cases (l_tl.nth_le 0 (list.nth_le._main._proof_1 l_hd l_tl 0 (nat.lt_pred_iff.mp a_proof))) = c,
  rw h at a,
  rw margin_eq_margin_minus_candidate,
  rw ←margin_eq_clone_non_clone P c D b d H H' clone,
  rw margin_eq_margin_minus_candidate, 
  rw ←margin_eq_clone_non_clone' P c D H not_d clone,
  exact a,

  specialize h'' h,
  rw margin_eq_margin_minus_candidate, rw margin_eq_margin_minus_candidate,
  rw ←margin_eq_clone_non_clone' P c D H not_d clone,
  rw margin_eq_clone_non_clone' P c D h'' not_d clone,
  rw ←margin_eq_clone_non_clone P c D b d H H' clone,
  rw ←margin_eq_margin_minus_candidate,
  exact a,

  rw dite_right_if h,
  rw margin_eq_margin_minus_candidate,
  rw ←margin_eq_clone_non_clone P c D b d H H' clone,
  exact a,
  exact h,

  rw [list.nth_le],
  specialize l_ih (i - 1),
  rw list.length_cons at i_bounds,
  simp only [nat.add_succ_sub_one, add_zero] at i_bounds,
  have o : ∀ i n, ¬ i = 0 → i < n → i - 1 < n - 1 := by omega,
  specialize l_ih (o i (replace_clones c D d H l_tl).length h i_bounds),
  rw nth_le_cons h,
  have o : ∀ i, ¬ i = 0 → i - 1 + 1 = i := by omega,
  simp_rw (o i h) at l_ih,
  exact l_ih,
end

-- A.5, would hold both directions. Added condition
lemma every_clone_defeats (b : {x : X // x ≠ c}) (e : b ∉ D) (d ∈ D) : clones P c D → ((split_cycle_VCCR V X P) c b ↔ (split_cycle_VCCR V X P) d b) :=
begin
  intro clone,
  rw split_cycle_definitions,
  unfold split_cycle_VCCR',
  split,
  intro w,
  introI f,
  cases w with m w,
  unfold margin_pos at m,
  rw margin_eq_clone_non_clone P c D b d H e clone at m,
  rw ←margin_eq_margin_minus_candidate at m,
  use m,
  push_neg, push_neg at w,
  intro l,
  specialize w (remove_clones c D l),
  intro ne_nil,
  specialize w ((remove_clones_ne_nil_iff c D l).mp ne_nil),
  contrapose w,
  push_neg, push_neg at w,
  use remove_clones_nodup c D l,
  cases w with l_nodup w,
  cases w with first w,
  cases w with last w,

  have f : ∀(p : ↑b ≠ c), (⟨↑b, p⟩ : {x : X // x ≠ c}) ∉ D,
  simp, intro _, exact e,

  use remove_clones_first_elem c D l ↑b f ne_nil first, 
  unfold remove_clones,
  rw to_path_last_elem,
  rw list.last_map,
  rw last,
  simp,
  have t : (¬↑d = c → d ∉ D → ↑d = c),
  intros x y,
  exfalso, exact y H,
  use t,
  exact remove_clones_chain'_of_chain' P c D l b e d H clone w,



  intro w,
  introI f,
  cases w with m w,
  unfold margin_pos at m,
  rw margin_eq_margin_minus_candidate at m,
  rw ←margin_eq_clone_non_clone P c D b d H e clone at m,
  use m,
  push_neg, push_neg at w,
  intros l ne_nil,
  specialize w (lift (replace_clones c D d H l)),
  have n1: (replace_clones c D d H l) ≠ list.nil,
  rw ←replace_clones_ne_nil_iff,
  exact ne_nil,

  have n : (lift (replace_clones c D d H l)) ≠ list.nil,
  rw lift_ne_nil_iff,
  exact n1,
  specialize w n,
  contrapose w,
  push_neg, push_neg at w,
  split,
  apply nodup_lift_of_nodup,
  apply replace_clones_nodup,
  cases w with nd w,
  cases w with first w,
  cases w with last w,

  split,
  unfold lift, unfold has_lift.lift,
  rw list.nth_le_map,
  rw replace_clones_first_elem c D l b,
  simp,
  push_neg, use b.property, simp, exact e,
  exact first,

  split,
  unfold lift, unfold has_lift.lift,
  rw list.last_eq_nth_le,
  rw list.nth_le_map,
  simp_rw list.length_map,
  rw ←list.last_eq_nth_le, 
  rw replace_clones_last_c c D l ne_nil,
  exact last,
  rw list.length_map, 
  have o : ∀ x : ℕ, 0 < x → x - 1 < x := by omega,
  apply o, apply list.length_pos_of_ne_nil, exact n1,
  have imp : ∀ (a b_1 : {x : X // x ≠ c}), (λ a b_1, margin P ↑d ↑b ≤ margin P (coe a) (coe b_1)) a b_1 → (λ a b_1, margin P ↑d ↑b ≤ margin P a b_1) (coe a) (coe b_1),
  intros a b_1 e, exact e,
  apply list.chain'_map_of_chain' coe imp,
  simp, 
  
  exact A5_chain P c D H e clone w,
end

lemma remove_clones'_cycle1 [fintype V] {l : list {x : X // x ≠ c}} {a' : {x : X // x ≠ c}} (H : a' ∉ D) {d : {x : X // x ≠ c}} (H' : d ∈ D) (clone : clones P c D) : list.chain' (λ (a_1 b : {x // x ≠ c}), margin (minus_candidate P c) a' d ≤ margin (minus_candidate P c) a_1 b) l
→ list.chain' (λ (a_1 b : X), margin P ↑a' c ≤ margin P a_1 b) (remove_clones' c D l) :=
begin
  intro a,
  induction l,
   {obviously,},
  unfold remove_clones',
  simp [to_path],
  specialize l_ih (and.right (list.chain'_cons'.mp a)),
  by_cases (list.index_of (ite (l_hd ∈ D) c ↑l_hd) (to_path (list.map (λ (x : {x // x ≠ c}), ite (x ∈ D) c ↑x) l_tl)) < (to_path (list.map (λ (x : {x // x ≠ c}), ite (x ∈ D) c ↑x) l_tl)).length),
  simp_rw (ite_left_if h),
  exact drop_chain'_of_chain' l_ih,

  simp_rw (ite_right_if h),
  by_cases j : l_tl = list.nil,
  rw j,
  rw list.map_nil,
  rw (to_path_eq_nil_iff list.nil).mpr,
  exact list.chain'_singleton (ite (l_hd ∈ D) c ↑l_hd),
  refl,

  rw list.chain'_iff_nth_le,
  rw list.chain'_iff_nth_le at l_ih,
  rw list.chain'_iff_nth_le at a,
  intros i i_bounds,
  have nodup := h,
  by_cases i = 0,
  have i_eq := h,
  simp_rw h,
  rw [list.nth_le], rw [list.nth_le],
  specialize a 0,
  have a_proof : 0 < (l_hd :: l_tl).length - 1,
  rw list.length_cons,
  simp only [nat.add_succ_sub_one, add_zero],
  exact (list.length_pos_of_ne_nil j),
  specialize a a_proof,
  rw [list.nth_le] at a, rw [list.nth_le] at a,
  have x := (to_path_first_elem {x : X // x ≠ c} l_tl j),
  rw to_path_first_elem',
  simp,
  
  by_cases (l_hd ∈ D),
  rw ite_left_if h,
  have h' := h,
  by_cases (l_tl.nth_le 0 _ ∈ D),
  exfalso,
  contrapose nodup,
  push_neg,
  rw list.index_of_lt_length,
  rw ite_left_if h',
  rw list.mem_iff_nth_le,
  use 0,
  have len : 0 < (to_path (list.map (λ (x : {x // x ≠ c}), ite (x ∈ D) c ↑x) l_tl)).length,
  change (0 < (remove_clones' c D l_tl).length),
  apply list.length_pos_of_ne_nil,
  rw ←remove_clones'_ne_nil_iff,
  exact j,
  use len,
  rw to_path_first_elem',
  rw list.nth_le_map (λ (x : {x // x ≠ c}), ite (x ∈ D) c ↑x) _ (list.length_pos_of_ne_nil j),
  simp,
  intro w,
  exfalso, exact w h,

  rw ite_right_if h,
  rw margin_eq_clone_non_clone' P c D H' H clone, 
  rw margin_eq_clone_non_clone P c D (l_tl.nth_le 0 _) l_hd h' h clone, 
  exact a,

  rw ite_right_if h,
  have h' := h,
  by_cases (l_tl.nth_le 0 _ ∈ D),
  rw ite_left_if h,
  rw margin_eq_clone_non_clone' P c D H' H clone, 
  rw margin_eq_clone_non_clone' P c D h h' clone, 
  exact a,

  rw ite_right_if h,
  rw margin_eq_clone_non_clone' P c D H' H clone, 
  rw margin_eq_margin_minus_candidate P,
  exact a,

  rw [list.nth_le],
  specialize l_ih (i - 1),
  rw list.length_cons at i_bounds,
  simp only [nat.add_succ_sub_one, add_zero] at i_bounds,
  have o : ∀ i n, ¬ i = 0 → i < n → i - 1 < n - 1 := by omega,
  specialize l_ih (o i (to_path (list.map (λ (x : {x // x ≠ c}), ite (x ∈ D) c ↑x) l_tl)).length h i_bounds),
  --change (margin P c ↑b ≤ margin P ((((ite (∀ (h : ¬l_hd = c), (⟨l_hd, h⟩ : {x : X // x ≠ c}) ∈ D) c l_hd)) :: (remove_clones c D l_tl)).nth_le i (nat.lt_of_lt_pred i_bounds)) ((remove_clones c D l_tl).nth_le i _)),
  rw nth_le_cons h,
  have o : ∀ i, ¬ i = 0 → i - 1 + 1 = i := by omega,
  simp_rw (o i h) at l_ih,
  exact l_ih,
end

lemma remove_clones'_cycle2 [fintype V] {l : list X} {a' : {x : X // x ≠ c}} (H : a' ∉ D) {d : {x : X // x ≠ c}} (H' : d ∈ D) (clone : clones P c D) : list.chain' (λ (a_1 b : X), margin P ↑a' c ≤ margin P a_1 b) l
→ list.chain' (λ (a_1 b : {x // x ≠ c}), margin (minus_candidate P c) a' d ≤ margin (minus_candidate P c) a_1 b) (replace_clones c D d H' l) :=
begin
  intro a,
  induction l,
    {obviously,},
  unfold replace_clones,
  simp [to_path],
  specialize l_ih (and.right (list.chain'_cons'.mp a)),
  by_cases @has_lt.lt.{0} nat nat.has_lt
  (@list.index_of.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
     (λ (a b : @subtype.{1} X (λ (x : X), @ne.{1} X x c)),
        classical.prop_decidable (@eq.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) a b))
     (@dite.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
        (∀ (h : not (@eq.{1} X l_hd c)),
           @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
             (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
             (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
             (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                   (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                      (iff.refl (@ne.{1} X l_hd c))
                      (not (@eq.{1} X l_hd c))
                      (@ne.def.{1} X l_hd c))
                   h))
             D)
        (@forall_prop_decidable (not (@eq.{1} X l_hd c))
           (λ (h : not (@eq.{1} X l_hd c)),
              @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                   (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                      (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                         (iff.refl (@ne.{1} X l_hd c))
                         (not (@eq.{1} X l_hd c))
                         (@ne.def.{1} X l_hd c))
                      h))
                D)
           (@ne.decidable.{1} X (λ (a b : X), classical.prop_decidable (@eq.{1} X a b)) l_hd c)
           (λ (h : not (@eq.{1} X l_hd c)),
              @set.decidable_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) D
                (λ (a : @subtype.{1} X (λ (x : X), @ne.{1} X x c)), classical.prop_decidable (D a))
                (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                   (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                      (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                         (iff.refl (@ne.{1} X l_hd c))
                         (not (@eq.{1} X l_hd c))
                         (@ne.def.{1} X l_hd c))
                      h))))
        (λ
         (h :
           ∀ (h : not (@eq.{1} X l_hd c)),
             @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
               (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
               (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
               (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                  (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                     (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                        (iff.refl (@ne.{1} X l_hd c))
                        (not (@eq.{1} X l_hd c))
                        (@ne.def.{1} X l_hd c))
                     h))
               D), d)
        (λ
         (h :
           not
             (∀ (h : not (@eq.{1} X l_hd c)),
                @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                  (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                  (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                  (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                     (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                        (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                           (iff.refl (@ne.{1} X l_hd c))
                           (not (@eq.{1} X l_hd c))
                           (@ne.def.{1} X l_hd c))
                        h))
                  D)),
           @subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
             (@replace_clones_helper X c D l_hd
                (@iff.mpr
                   (not
                      (∀ (p : @ne.{1} X l_hd c),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd p)
                           D))
                   (not
                      (∀ (h : not (@eq.{1} X l_hd c)),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                              (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                                    (iff.refl (@ne.{1} X l_hd c))
                                    (not (@eq.{1} X l_hd c))
                                    (@ne.def.{1} X l_hd c))
                                 h))
                           D))
                   (@not_iff_not_of_iff
                      (∀ (p : @ne.{1} X l_hd c),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd p)
                           D)
                      (∀ (h : not (@eq.{1} X l_hd c)),
                         @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                           (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                           (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd
                              (@iff.mpr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                                    (iff.refl (@ne.{1} X l_hd c))
                                    (not (@eq.{1} X l_hd c))
                                    (@ne.def.{1} X l_hd c))
                                 h))
                           D)
                      (@forall_prop_congr (@ne.{1} X l_hd c) (not (@eq.{1} X l_hd c))
                         (λ (h : @ne.{1} X l_hd c),
                            @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                              (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd h)
                              D)
                         (λ (h : @ne.{1} X l_hd c),
                            @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                              (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                              (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd h)
                              D)
                         (λ (h : @ne.{1} X l_hd c),
                            iff.refl
                              (@has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                 (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                 (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                 (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) l_hd h)
                                 D))
                         (@eq.rec.{0 1} Prop (@ne.{1} X l_hd c) (λ (A : Prop), iff (@ne.{1} X l_hd c) A)
                            (iff.refl (@ne.{1} X l_hd c))
                            (not (@eq.{1} X l_hd c))
                            (@ne.def.{1} X l_hd c))))
                   h))))
     (@to_path (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
        (@list.map.{0 0} X (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
           (λ (x : X),
              @dite.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                (∀ (h : not (@eq.{1} X x c)),
                   @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                     (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                        (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                           (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                              (iff.refl (@ne.{1} X x c))
                              (not (@eq.{1} X x c))
                              (@ne.def.{1} X x c))
                           h))
                     D)
                (@forall_prop_decidable (not (@eq.{1} X x c))
                   (λ (h : not (@eq.{1} X x c)),
                      @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                        (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))
                        D)
                   (@ne.decidable.{1} X (λ (a b : X), classical.prop_decidable (@eq.{1} X a b)) x c)
                   (λ (h : not (@eq.{1} X x c)),
                      @set.decidable_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) D
                        (λ (a : @subtype.{1} X (λ (x : X), @ne.{1} X x c)), classical.prop_decidable (D a))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))))
                (λ
                 (h :
                   ∀ (h : not (@eq.{1} X x c)),
                     @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                       (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                          (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                             (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                (iff.refl (@ne.{1} X x c))
                                (not (@eq.{1} X x c))
                                (@ne.def.{1} X x c))
                             h))
                       D), d)
                (λ
                 (h :
                   not
                     (∀ (h : not (@eq.{1} X x c)),
                        @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                          (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                             (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                   (iff.refl (@ne.{1} X x c))
                                   (not (@eq.{1} X x c))
                                   (@ne.def.{1} X x c))
                                h))
                          D)),
                   @subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                     (@replace_clones_helper X c D x
                        (@iff.mpr
                           (not
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D))
                           (not
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D))
                           (@not_iff_not_of_iff
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D)
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D)
                              (@forall_prop_congr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    iff.refl
                                      (@has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                         (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                         D))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                    (iff.refl (@ne.{1} X x c))
                                    (not (@eq.{1} X x c))
                                    (@ne.def.{1} X x c))))
                           h))))
           l_tl)))
  (@list.length.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
     (@to_path (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
        (@list.map.{0 0} X (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
           (λ (x : X),
              @dite.{1} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                (∀ (h : not (@eq.{1} X x c)),
                   @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                     (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                     (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                        (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                           (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                              (iff.refl (@ne.{1} X x c))
                              (not (@eq.{1} X x c))
                              (@ne.def.{1} X x c))
                           h))
                     D)
                (@forall_prop_decidable (not (@eq.{1} X x c))
                   (λ (h : not (@eq.{1} X x c)),
                      @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                        (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))
                        D)
                   (@ne.decidable.{1} X (λ (a b : X), classical.prop_decidable (@eq.{1} X a b)) x c)
                   (λ (h : not (@eq.{1} X x c)),
                      @set.decidable_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)) D
                        (λ (a : @subtype.{1} X (λ (x : X), @ne.{1} X x c)), classical.prop_decidable (D a))
                        (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                           (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                              (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                 (iff.refl (@ne.{1} X x c))
                                 (not (@eq.{1} X x c))
                                 (@ne.def.{1} X x c))
                              h))))
                (λ
                 (h :
                   ∀ (h : not (@eq.{1} X x c)),
                     @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                       (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                       (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                          (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                             (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                (iff.refl (@ne.{1} X x c))
                                (not (@eq.{1} X x c))
                                (@ne.def.{1} X x c))
                             h))
                       D), d)
                (λ
                 (h :
                   not
                     (∀ (h : not (@eq.{1} X x c)),
                        @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                          (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                          (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                             (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                   (iff.refl (@ne.{1} X x c))
                                   (not (@eq.{1} X x c))
                                   (@ne.def.{1} X x c))
                                h))
                          D)),
                   @subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                     (@replace_clones_helper X c D x
                        (@iff.mpr
                           (not
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D))
                           (not
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D))
                           (@not_iff_not_of_iff
                              (∀ (p : @ne.{1} X x c),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x p)
                                   D)
                              (∀ (h : not (@eq.{1} X x c)),
                                 @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                   (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                   (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x
                                      (@iff.mpr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                         (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                            (iff.refl (@ne.{1} X x c))
                                            (not (@eq.{1} X x c))
                                            (@ne.def.{1} X x c))
                                         h))
                                   D)
                              (@forall_prop_congr (@ne.{1} X x c) (not (@eq.{1} X x c))
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    @has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                      (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                      (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                      D)
                                 (λ (h : @ne.{1} X x c),
                                    iff.refl
                                      (@has_mem.mem.{0 0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c))
                                         (set.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@set.has_mem.{0} (@subtype.{1} X (λ (x : X), @ne.{1} X x c)))
                                         (@subtype.mk.{1} X (λ (x : X), @ne.{1} X x c) x h)
                                         D))
                                 (@eq.rec.{0 1} Prop (@ne.{1} X x c) (λ (A : Prop), iff (@ne.{1} X x c) A)
                                    (iff.refl (@ne.{1} X x c))
                                    (not (@eq.{1} X x c))
                                    (@ne.def.{1} X x c))))
                           h))))
           l_tl))),

  simp_rw (ite_left_if h),
  exact drop_chain'_of_chain' l_ih,

  simp_rw (ite_right_if h),
  by_cases j : l_tl = list.nil,
  rw j,
  simp [to_path],
  
  rw list.chain'_iff_nth_le,
  rw list.chain'_iff_nth_le at l_ih,
  rw list.chain'_iff_nth_le at a,
  intros i i_bounds,
  rename h nodup,
  by_cases i = 0,
  rename h i_eq,
  simp_rw i_eq,
  rw [list.nth_le], rw [list.nth_le],
  specialize a 0,
  have a_proof : 0 < (l_hd :: l_tl).length - 1,
  rw list.length_cons,
  simp only [nat.add_succ_sub_one, add_zero],
  exact (list.length_pos_of_ne_nil j),
  specialize a a_proof,
  rw [list.nth_le] at a, rw [list.nth_le] at a,
  have x := (to_path_first_elem X l_tl j),
  rw to_path_first_elem',
  simp,
  
  split_ifs with h',
  by_cases (∀ (h_1 : ¬l_tl.nth_le 0 (list.length_pos_of_ne_nil j) = c), (⟨l_tl.nth_le 0 (list.length_pos_of_ne_nil j), h_1⟩ : {x : X // x ≠ c}) ∈ D),
  exfalso,
  contrapose nodup,
  push_neg,
  rw list.index_of_lt_length,
  rw dite_left_if h',
  rw list.mem_iff_nth_le,
  use 0,
  have len : (0 < (replace_clones c D d H' l_tl).length),
  apply list.length_pos_of_ne_nil,
  rw ←replace_clones_ne_nil_iff,
  exact j,
  use len,
  rw to_path_first_elem',
  rw list.nth_le_map (λ (x : X), dite (∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D) (λ (h : ∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D), d) (λ (h : ¬∀ (h : ¬x = c), (⟨x, h⟩ : {x : X // x ≠ c}) ∈ D), ⟨x, replace_clones_helper c D h⟩)) _ (list.length_pos_of_ne_nil j),
  simp,
  rw dite_left_if h,

  rw dite_right_if h,

  push_neg at h,
  cases h with not_c not_d,
  by_cases l_hd = c,
  rw h at a,
  rw ←margin_eq_clone_non_clone' P c D H' H clone,
  rw ←margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ d H' not_d clone,
  exact a,


  specialize h' h,
  rw ←margin_eq_clone_non_clone' P c D H' H clone,
  rw ←margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ d H' not_d clone,
  rw margin_eq_clone_non_clone P c D ⟨l_tl.nth_le 0 _, not_c⟩ ⟨l_hd, h⟩ h' not_d clone,
  rw ←margin_eq_margin_minus_candidate,
  exact a,
  exact h,

  by_cases (∀ (h_1 : ¬l_tl.nth_le 0 (list.length_pos_of_ne_nil j) = c), (⟨l_tl.nth_le 0 (list.length_pos_of_ne_nil j), h_1⟩ : {x : X // x ≠ c}) ∈ D),
  rw dite_left_if h,
  push_neg at h',
  cases h' with not_c not_d,
  rename h h'',
  by_cases (l_tl.nth_le 0 (list.nth_le._main._proof_1 l_hd l_tl 0 (nat.lt_pred_iff.mp a_proof))) = c,
  rw h at a,
  rw ←margin_eq_clone_non_clone' P c D H' H clone,
  rw ←margin_eq_clone_non_clone' P c D H' not_d clone,
  exact a,

  specialize h'' h,
  rw ←margin_eq_clone_non_clone' P c D H' H clone,
  rw ←margin_eq_clone_non_clone' P c D H' not_d clone,
  rw margin_eq_clone_non_clone' P c D h'' not_d clone,
  rw ←margin_eq_margin_minus_candidate,
  exact a,

  rw dite_right_if h,
  rw ←margin_eq_clone_non_clone' P c D H' H clone,
  rw ←margin_eq_margin_minus_candidate,
  exact a,
  exact h,

  rw [list.nth_le],
  specialize l_ih (i - 1),
  rw list.length_cons at i_bounds,
  simp only [nat.add_succ_sub_one, add_zero] at i_bounds,
  have o : ∀ i n, ¬ i = 0 → i < n → i - 1 < n - 1 := by omega,
  specialize l_ih (o i (replace_clones c D d H' l_tl).length h i_bounds),
  rw nth_le_cons h,
  have o : ∀ i, ¬ i = 0 → i - 1 + 1 = i := by omega,
  simp_rw (o i h) at l_ih,
  exact l_ih,
end

lemma every_clone_defeated' (a : {x : X // x ≠ c}) (e : a ∉ D) (d ∈ D) : clones P c D → ((split_cycle_VCCR V X P) a c ↔ (split_cycle_VCCR V {x : X // x ≠ c} (minus_candidate P c)) a d) :=
begin
  intro clone,
  rw split_cycle_definitions,
  unfold split_cycle_VCCR',
  split,
  intro w,
  introI f,
  cases w with m w,
  unfold margin_pos at m,
  rw margin_eq_clone_non_clone' P c D H e clone at m,
  rw ←margin_eq_margin_minus_candidate at m,
  use m,
  push_neg, push_neg at w,
  intro l,
  specialize w (remove_clones' c D l),
  intro ne_nil,
  specialize w ((remove_clones'_ne_nil_iff c D l).mp ne_nil),
  contrapose w,
  push_neg, push_neg at w,
  use remove_clones'_nodup c D l,
  cases w with l_nodup w,
  cases w with first w,
  cases w with last w,

  split,
  unfold remove_clones',
  rw to_path_first_elem',
  rw list.nth_le_map,
  simp_rw first,
  split_ifs,
  refl,
  exact list.length_pos_of_ne_nil ne_nil,
  use remove_clones'_last_elem c D l a e ne_nil last, 
  exact remove_clones'_cycle1 P c D e H clone w,

  intro w,
  introI f,
  cases w with m w,
  unfold margin_pos at m,
  rw ←margin_eq_clone_non_clone' P c D H e clone at m,
  use m,
  push_neg, push_neg at w,
  intros l ne_nil,
  specialize w (replace_clones c D d H l),
  have n: (replace_clones c D d H l) ≠ list.nil,
  rw ←replace_clones_ne_nil_iff,
  exact ne_nil,

  specialize w n,
  contrapose w,
  push_neg, push_neg at w,
  split,
  apply replace_clones_nodup,
  cases w with nd w,
  cases w with first w,
  cases w with last w,

  split,
  unfold replace_clones,
  rw to_path_first_elem,
  rw list.nth_le_map,
  split_ifs,
  refl,
  push_neg at h,
  cases h with contr h,
  exfalso,
  exact contr first,
  simp,
  exact ne_nil,

  rw replace_clones_last_elem c D l a,
  simp,
  
  exact remove_clones'_cycle2 P c D e H clone w,
  push_neg,
  use a.property,
  simp, exact e,
  exact last,
end
--set_option pp.all true 

theorem non_clone_choice_ind_clones_split_cyle [fintype V] : non_clone_choice_ind_clones P c D split_cycle :=
begin
  unfold non_clone_choice_ind_clones,
  intro clone,
  intro a, intro not_d,

  unfold split_cycle,
  unfold max_el_VSCC,
  simp,
  split,
  intro d,
  contrapose d,
  push_neg at d, push_neg,
  cases d with b d,
  cases d with b_c d,
  use b,
  have test := (clone_maintains_defeat P c D ⟨b, b_c⟩ a not_d clone).mp, 
  simp at test,
  apply test,
  introI _inst_1,
  exact d,

  intro d,
  contrapose d,
  push_neg at d, push_neg,
  cases d with b d,
  by_cases b = c,
  have clone' := clone,
  unfold clones at clone',
  cases clone' with n clone',
  use n.some,
  use n.some.property,
  simp,
  apply (clone_maintains_defeat P c D n.some a not_d clone).mpr, 
  have test := every_clone_defeats P c D a not_d n.some n.some_spec clone, 
  apply test.mp,
  rw h at d,
  introI _inst_1,
  exact d,

  use b,
  use h,
  have test := (clone_maintains_defeat P c D ⟨b, h⟩ a not_d clone).mpr, 
  simp at test,
  apply test,
  introI _inst_1,
  exact d,
end

theorem clone_choice_ind_clones_split_cyle [fintype V] [fintype X] : clone_choice_ind_clones P c D split_cycle :=
begin
   unfold clone_choice_ind_clones,
   intro clone, 
   split,
   intro a,
   cases a with a1 a2,

   have spec : ∀ h : c ≠ c, (⟨c, h⟩ : {x // x ≠ c}) ∈ D,
      {intro contr, exfalso, exact contr (eq.refl c), },
   by_cases ∀ c' : {x // ∀ h : x ≠ c, (⟨x, h⟩ : {x // x ≠ c}) ∈ D}, ∃ d : {x // ∀ h : x ≠ c, (⟨x, h⟩ : {x // x ≠ c}) ∈ D}, split_cycle_VCCR V X P d c',
   have clone' := clone,
   cases clone' with n clone,
   let f : {x // ∀ h : x ≠ c, (⟨x, h⟩ : {x // x ≠ c}) ∈ D} → {x // ∀ h : x ≠ c, (⟨x, h⟩ : {x // x ≠ c}) ∈ D} := λ x, (h x).some,
   let seq := stream.iterate f ⟨c, spec⟩,
   have property : ∀ x : ℕ, split_cycle_VCCR V X P (seq.nth x.succ) (seq.nth x),
      {intro i,
      change split_cycle_VCCR V X P ((h (seq.nth i)).some) (seq.nth i),
      have test := (h (seq.nth i)).some_spec,

      unfold split_cycle_VCCR, intro f, 
      unfold margin_pos,
      simp_rw margin_eq_margin f _inst_1,
      exact test,},

   let seq2 : stream X := λ (x : ℕ), (seq.nth x).val,
   exfalso, 
   exact false_of_sequence_acyclic_vccr (split_cycle_VCCR_acyclic P) seq2 property,

   push_neg at h,
   cases h with d h,
   unfold split_cycle at a1,
   unfold max_el_VSCC at a1,
   unfold split_cycle at a2, unfold max_el_VSCC at a2,
   simp at a2,
   simp at a1,
   have some_a : ∃ a, (∃ h: a ≠ c, (⟨a, h⟩ : {x // x ≠ c}) ∉ D) ∧ split_cycle_VCCR V X P a d, 
      {by_cases h': ↑d = c, cases a1 with x a1, use x, 
      split, contrapose h, push_neg, simp at h,
      use ⟨x, h⟩, rw h', simp, intro f, 
      unfold margin_pos, simp_rw margin_eq_margin f _inst_1,
      exact a1, rw h', intro f, 
      unfold margin_pos, simp_rw margin_eq_margin f _inst_1,
      exact a1,

      specialize a2 d, specialize a2 h', specialize a2 (d.property h'),
      cases a2 with a a2,
      use a,
      split, contrapose h, simp, simp at h,
      use a, use h, intro f, 
      unfold margin_pos, simp_rw margin_eq_margin f _inst_1,
      exact a2, intro f, 
      unfold margin_pos, simp_rw margin_eq_margin f _inst_1,
      exact a2,
      },

   intros e e_D, 
   unfold split_cycle, unfold max_el_VSCC, simp,
   cases some_a with a some_a,
   use a,
   cases some_a with some_a defeats,
   cases some_a with not_c some_a,
   use not_c,
   by_cases ↑d = c,
   rw ←every_clone_defeated' P c D ⟨a, not_c⟩ some_a e e_D clone,
   simp_rw ←h, intro f,
   unfold margin_pos,
   simp_rw margin_eq_margin f _inst_1, 
   exact defeats,
   rw ←every_clone_defeated' P c D ⟨a, not_c⟩ some_a e e_D clone,
   rw every_clone_defeated' P c D ⟨a, not_c⟩ some_a ⟨↑d, h⟩ (d.property h) clone,
   rw clone_maintains_defeat' P c D ⟨a, not_c⟩ ⟨↑d, h⟩ some_a (d.property h) clone,
   intro f,
   unfold margin_pos,
   simp_rw margin_eq_margin f _inst_1, 
   exact defeats,
   intro a,

   by_cases ∀ c' : {x // x ∈ D}, ∃ d : {x // x ∈ D}, split_cycle_VCCR V {x : X // x ≠ c} (minus_candidate P c) d c',
   have clone' := clone,
   cases clone' with n clone,
   let f : {x // x ∈ D} → {x // x ∈ D} := λ x, (h x).some,
   let seq := stream.iterate f ⟨n.some, n.some_spec⟩,
   have property : ∀ x : ℕ, split_cycle_VCCR V {x : X // x ≠ c} (minus_candidate P c) (seq.nth x.succ) (seq.nth x),
      {intro i,
      change split_cycle_VCCR V {x : X // x ≠ c} (minus_candidate P c) ((h (seq.nth i)).some) (seq.nth i),
      have test := (h (seq.nth i)).some_spec,

      unfold split_cycle_VCCR, intro f, 
      unfold margin_pos,
      simp_rw margin_eq_margin f _inst_1,
      exact test,},

   let seq2 : stream {x : X // x ≠ c} := λ (x : ℕ), (seq.nth x).val,
   exfalso, 
   exact false_of_sequence_acyclic_vccr (split_cycle_VCCR_acyclic (minus_candidate P c)) seq2 property,

   push_neg at h,
   cases h with d h,
   unfold split_cycle at a,
   unfold max_el_VSCC at a,
   simp at a,
   have some_a : ∃ a ∉ D, split_cycle_VCCR V {x : X // x ≠ c} (minus_candidate P c) a d, 
      {
      specialize a d, specialize a d.val.property, simp at a,
      cases a with a' a,
      use a', cases a with not_c a,
      exact not_c,
      split, contrapose h, simp, simp at h,
      use a', cases a with not_c a, use not_c, use h, intro f,
      unfold margin_pos, simp_rw margin_eq_margin f _inst_1,
      exact a, intro f, 
      unfold margin_pos, simp_rw margin_eq_margin f _inst_1,
      cases a with not_c a,
      exact a,
      },


   unfold split_cycle, unfold max_el_VSCC, simp,
   split,
   cases some_a with a some_a,
   cases some_a with H some_a,
   use ↑a,
   rw every_clone_defeated' P c D a H d.val d.property clone,
   intro f, unfold margin_pos, simp_rw margin_eq_margin f _inst_1,
   exact some_a,

   intros a not_c in_d, 
   cases some_a with a' some_a,
   use a',
   cases some_a with not_d defeats,
   have test := clone_maintains_defeat' P c D a' ⟨a, not_c⟩ not_d in_d clone,
   simp at test,
   rw ←test,
   rw ←every_clone_defeated' P c D a' not_d ⟨a, not_c⟩ in_d clone,
   rw every_clone_defeated' P c D a' not_d d.val d.property clone,
   intro f, unfold margin_pos, simp_rw margin_eq_margin f _inst_1,
   exact defeats,
end