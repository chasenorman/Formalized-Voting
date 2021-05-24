import main
import split_cycle

open_locale classical

variables {V X : Type}

def minus_voter (P : Prof V X) (i : V) : Prof {v : V // v ≠ i} X := λ v x y, P v.val x y
-- use strict preference.
def positive_involvement (F : VSCC) (P : Prof V X) : Prop := ∀ (x : X) (i : V), x ∈ F {v : V // v ≠ i} X (minus_voter P i) → (∀ y, y ≠ x → P i x y) → x ∈ F V X P

def negative_involvement (F : VSCC) (P : Prof V X) : Prop := ∀ (x : X) (i : V), x ∉ F {v : V // v ≠ i} X (minus_voter P i) → (∀ y, y ≠ x → P i y x) → x ∉ F V X P

lemma minus_voter_margin_eq [fintype V] (i : V) [fintype {v // v ≠ i}] (P : Prof V X) [profile_asymmetric P] (z x : X) (p : P i x z) : margin (minus_voter P i) z x = margin P z x + 1 :=
begin
  have asymm := _inst_3.asymmetric,
  unfold margin,
  have meq : ((finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 z x) finset.univ).card) = ((finset.filter (λ (x_1 : V), P x_1 z x) finset.univ).card),
    {apply eq.symm,
    have f : (finset.filter (λ (x_1 : V), P x_1 z x) finset.univ) = (finset.map ⟨(λ (s : {v // v ≠ i}), s.val), begin
      obviously,
    end⟩ (finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 z x) finset.univ)),
      {simp, ext1, obviously, 
      rw ←ᾰ_1 at p, 
      exact (asymm a z x ᾰ) p, }, -- require asymmetry
      rw f,
      simp,},
  rw meq,
  have o : ∀ a b c : ℤ, c = b + 1 → a - b = a - c + 1 := by omega,
  apply o (↑((finset.filter (λ (x_1 : V), P x_1 z x) finset.univ).card)) (↑((finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 x z) finset.univ).card)) (↑((finset.filter (λ (x_1 : V), P x_1 x z) finset.univ).card)),
  norm_cast,
  rw finset.card_eq_succ,
  use i, use (finset.filter (λ (x_1 : V), x_1 ≠ i ∧ P x_1 x z) finset.univ),
  have nmem : i ∉ (finset.filter (λ (x_1 : V), x_1 ≠ i ∧ P x_1 x z) finset.univ),
    {obviously,},

  use nmem,
  split,
  ext1,
  simp only [true_and, finset.mem_univ, ne.def, finset.mem_insert, finset.mem_filter],

  split,
    {intro m,
    cases m,
    rw m, 
    exact p,
    exact and.right m,},
    {intro m,
    by_cases a = i,
    use h,
    apply or.inr,
    exact ⟨h, m⟩,},

  refine finset.card_congr _ _ _ _,
    {intro a,
    intro a_spec,
    simp at a_spec,
    exact ⟨a, and.left a_spec⟩,},
    {intro a, intro ha, simp at ha, simp, 
    unfold minus_voter, simp, exact and.right ha,},
    {intros a b ha hb, simp at ha, simp at hb,
    simp, },
    {intros b hb, simp at hb, simp,
    use b.val, simp, use b.property, unfold minus_voter at hb,
    exact hb,},
end

lemma minus_voter_margin_le [fintype V] (i : V) [fintype {v // v ≠ i}] (P : Prof V X) [profile_asymmetric P] (a b : X) : margin (minus_voter P i) a b ≤ margin P a b + 1 :=
begin
  by_cases P i b a,
    {have m := minus_voter_margin_eq i P a b h,
    exact le_of_eq m,},

  unfold margin,
  
  have meq : ((finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 b a) finset.univ).card) = ((finset.filter (λ (x_1 : V), P x_1 b a) finset.univ).card),
    {refine finset.card_congr _ _ _ _,
      {intros a a_spec,
      exact a.val,},
      {intros a_1 ha, simp, simp at ha, unfold minus_voter at ha, exact ha, },
      {intros a_1 b_1 ha hb, simp, obviously,},
      {intros b_1 b_spec, simp at b_spec, 
      let h2 := h,
      by_cases b_1 = i,
      exfalso, rw h at b_spec, exact h2 b_spec, 
      use ⟨b_1, h⟩,
      split, simp, simp, unfold minus_voter, exact b_spec,},
    },

  rw meq, 
  have o : ∀ a b c : ℤ, a ≤ c → a - b ≤ c - b + 1 := by omega,
  apply o (↑((finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 a b) finset.univ).card)) (↑((finset.filter (λ (x_1 : V), P x_1 b a) finset.univ).card)) (↑((finset.filter (λ (x_1 : V), P x_1 a b) finset.univ).card)),

  norm_cast,
  refine finset.card_le_card_of_inj_on _ _ _,
  exact (λ v, v.val),
  intros a_1 a_spec,
  simp, simp at a_spec,
  unfold minus_voter at a_spec,
  exact a_spec,

  intros a1 a1_spec a2 a2_spec,
  obviously,
end

theorem positive_involvement_split_cycle [fintype V] (P : Prof V X) [profile_asymmetric P] : positive_involvement split_cycle P :=
begin
  unfold positive_involvement,
  intros x i w p,
  unfold split_cycle, unfold max_el_VSCC, unfold split_cycle_VCCR, simp,
  unfold split_cycle at w, unfold max_el_VSCC at w, unfold split_cycle_VCCR at w, 
  unfold split_cycle_CCR at w, simp at w,
  intro y, 
  unfold split_cycle_CCR,
  push_neg,
  use _inst_1,
  intro m,
  specialize w y,

  casesI w with _inst_3 w,

  have ynx := ne_of_margin_pos m,

  have mxy := minus_voter_margin_eq i P y x (p y ynx),

  have mp : margin_pos (minus_voter P i) y x,
    {unfold margin_pos, rw mxy, 
    have o : ∀ a : ℤ, a > 0 → 0 < a + 1 := by omega,
    exact o (margin P y x) m,},
  
  specialize w mp,
  cases w with c w,
  cases w with x_mem w,
  cases w with y_mem w,

  use c, use x_mem, use y_mem,

  refine cycle_of_cycle_imp _ w,
  intros a b mab,
  have o : ∀ a b c d : ℤ, a ≤ b → a = c + 1 → b ≤ d + 1 → c ≤ d := by omega,

  apply (o (margin (minus_voter P i) y x) (margin (minus_voter P i) a b) (margin P y x) (margin P a b) mab mxy ),

  exact minus_voter_margin_le i P a b,
end

lemma minus_voter_margin_eq2 [fintype V] (i : V) [fintype {v // v ≠ i}] (P : Prof V X) [profile_asymmetric P] (z x : X) (p : P i z x) : margin (minus_voter P i) z x + 1 = margin P z x :=
begin
  have asymm := _inst_3.asymmetric,
  unfold margin,
  have meq : ((finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 x z) finset.univ).card) = ((finset.filter (λ (x_1 : V), P x_1 x z) finset.univ).card),
    {apply eq.symm,
    have f : (finset.filter (λ (x_1 : V), P x_1 x z) finset.univ) = (finset.map ⟨(λ (s : {v // v ≠ i}), s.val), begin
      obviously,
    end⟩ (finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 x z) finset.univ)),
      {simp, ext1, obviously, 
      rw ←ᾰ_1 at p, 
      exact (asymm a x z ᾰ) p, }, -- require asymmetry
      rw f,
      simp,},
  rw meq,
  have o : ∀ a b c : ℤ, c = a + 1 → a - b + 1 = c - b := by omega,
  apply o (↑((finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 z x) finset.univ).card)) (↑((finset.filter (λ (x_1 : V), P x_1 x z) finset.univ).card)) (↑((finset.filter (λ (x_1 : V), P x_1 z x) finset.univ).card)),
  norm_cast,
  rw finset.card_eq_succ,
  use i, use (finset.filter (λ (x_1 : V), x_1 ≠ i ∧ P x_1 z x) finset.univ),
  have nmem : i ∉ (finset.filter (λ (x_1 : V), x_1 ≠ i ∧ P x_1 z x) finset.univ),
    {obviously,},

  use nmem,
  split,
  ext1,
  simp only [true_and, finset.mem_univ, ne.def, finset.mem_insert, finset.mem_filter],

  split,
    {intro m,
    cases m,
    rw m, 
    exact p,
    exact and.right m,},
    {intro m,
    by_cases a = i,
    use h,
    apply or.inr,
    exact ⟨h, m⟩,},

  refine finset.card_congr _ _ _ _,
    {intro a,
    intro a_spec,
    simp at a_spec,
    exact ⟨a, and.left a_spec⟩,},
    {intro a, intro ha, simp at ha, simp, 
    unfold minus_voter, simp, exact and.right ha,},
    {intros a b ha hb, simp at ha, simp at hb,
    simp, },
    {intros b hb, simp at hb, simp,
    use b.val, simp, use b.property, unfold minus_voter at hb,
    exact hb,},
end

lemma minus_voter_margin_le2 [fintype V] (i : V) [fintype {v // v ≠ i}] (P : Prof V X) [profile_asymmetric P] (a b : X) : margin P a b ≤ margin (minus_voter P i) a b + 1 :=
begin
  by_cases P i a b,
    {have m := minus_voter_margin_eq2 i P a b h,
    exact le_of_eq m.symm,},

  unfold margin,
  
  have meq : ((finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 a b) finset.univ).card) = ((finset.filter (λ (x_1 : V), P x_1 a b) finset.univ).card),
    {refine finset.card_congr _ _ _ _,
      {intros a a_spec,
      exact a.val,},
      {intros a_1 ha, simp, simp at ha, unfold minus_voter at ha, exact ha, },
      {intros a_1 b_1 ha hb, simp, obviously,},
      {intros b_1 b_spec, simp at b_spec, 
      let h2 := h,
      by_cases b_1 = i,
      exfalso, rw h at b_spec, exact h2 b_spec, 
      use ⟨b_1, h⟩,
      split, simp, simp, unfold minus_voter, exact b_spec,},
    },

  rw meq, 
  have o : ∀ a b c : ℤ, c ≤ b → a - b ≤ a - c + 1 := by omega,
  apply o (↑((finset.filter (λ (x_1 : V), P x_1 a b) finset.univ).card)) (↑((finset.filter (λ (x_1 : V), P x_1 b a) finset.univ).card)) (↑((finset.filter (λ (x_1 : {v // v ≠ i}), minus_voter P i x_1 b a) finset.univ).card)),

  norm_cast,
  refine finset.card_le_card_of_inj_on _ _ _,
  exact (λ v, v.val),
  intros a_1 a_spec,
  simp, simp at a_spec,
  unfold minus_voter at a_spec,
  exact a_spec,

  intros a1 a1_spec a2 a2_spec,
  obviously,
end

theorem negative_involvement_split_cycle [fintype V] (P : Prof V X) [profile_asymmetric P] : negative_involvement split_cycle P :=
begin
  intros x i w p,
  unfold split_cycle, unfold max_el_VSCC, unfold split_cycle_VCCR, simp,
  unfold split_cycle at w, unfold max_el_VSCC at w, unfold split_cycle_VCCR at w, 
  unfold split_cycle_CCR at w, simp at w,
  cases w with y w,
  use y,
  introI _inst_3,
  specialize w (subtype.fintype (λ v, v ≠ i)),
  cases w with m w,

  have ynx := ne_of_margin_pos m,
  have mxy := minus_voter_margin_eq2 i P y x (p y ynx),

  have o : ∀ a b : ℤ, 0 < a → a + 1 = b → 0 < b := by omega,
  use o (margin (minus_voter P i) y x) (margin P y x) m mxy,
  push_neg,
  intros l x_mem y_mem,
  specialize w l, specialize w x_mem, specialize w y_mem,
  contrapose w,
  push_neg,
  push_neg at w,

  refine cycle_of_cycle_imp _ w,
  intros a b mab,

  have o : ∀ a b c d : ℤ, a ≤ b → c + 1 = a → b ≤ d + 1 → c ≤ d := by omega,

  apply (o (margin P y x) (margin P a b) (margin (minus_voter P i) y x) (margin (minus_voter P i) a b) mab mxy ),

  exact minus_voter_margin_le2 i P a b,
end