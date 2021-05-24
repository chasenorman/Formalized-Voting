import main
import split_cycle

open_locale classical

variables {V X : Type} 

-- x P' y ↔ y P x
def reverse_profile : Prof V X → Prof V X := λ P v x y, P v y x -- is there a name for the inverse? 

def reversal_symmetry (F : VSCC) (P : Prof V X) : Prop := ∀ x, (∃ y, x ≠ y) → (F V X P = {x}) → (x ∉ F V X (reverse_profile P))

lemma margin_reverse_eq [fintype V] (P : Prof V X) (a b : X) : margin (reverse_profile P) b a = margin P a b :=
begin
  obviously,
end

-- fintype V shouldn't be necessary.
theorem split_cycle_reversal_symmetry [fintype V] [fintype X] (P : Prof V X): reversal_symmetry split_cycle P := 
begin 
  rintros x e win,
  cases e with y n,
  unfold split_cycle,
  unfold max_el_VSCC,
  simp,
  unfold split_cycle_VCCR, unfold split_cycle_CCR,
  simp,


  unfold split_cycle at win,
  unfold max_el_VSCC at win,
  --unfold split_cycle_VCCR at win,
  --simp at win,

  have defeats : ∃ z, split_cycle_VCCR V X P x z,
    {by_contradiction,
    push_neg at h,

    have defeated : ∀ w, x ≠ w → ∃ a, split_cycle_VCCR V X P a w,
      {intros w nw,
      by_contradiction,
      push_neg at h,

      have within : w ∈ {x : X | ∀ (y : X), ¬split_cycle_VCCR V X P y x},
        {simp,
        exact h,},

      rw win at within,
      exact nw (eq.symm (set.eq_of_mem_singleton within)),},

    have ndefeated : ∀ w (e : x ≠ w), x ≠ (defeated w e).some,
      {intros w e,
      by_contradiction h2,
      push_neg at h2,
      have c := (classical.indefinite_description (λ a, split_cycle_VCCR V X P a w) (defeated w e)).property,
      specialize h w,
      rw h2 at h, 
      change split_cycle_VCCR V X P (defeated w e).some w at c,
      unfold split_cycle_VCCR at h, unfold split_cycle_CCR at h, push_neg at h, cases h with f h,
      unfold split_cycle_VCCR at c, unfold split_cycle_CCR at c, contrapose c,
      push_neg, use f,
      exact h,},


    let s : {b : X // x ≠ b} → {b : X // x ≠ b} := λ (a : {b : X // x ≠ b}), ⟨(defeated a a.property).some, ndefeated a a.property⟩,
    let seq := stream.iterate s ⟨y, n⟩,
    have property : ∀ x : ℕ, split_cycle_VCCR V X P (seq.nth x.succ) (seq.nth x),
      {intro i,
      change split_cycle_VCCR V X P (classical.some (defeated (seq.nth i) (seq.nth i).property)) (seq.nth i),
      have w := classical.some_spec (defeated (seq.nth i) (seq.nth i).property),
      unfold split_cycle_VCCR, intro f, 
      unfold margin_pos,
      simp_rw margin_eq_margin f _inst_1,
      exact w,},
    
    let seq2 : stream X := λ (x : ℕ), (seq.nth x).val,

    exact false_of_sequence_acyclic_vccr (split_cycle_VCCR_acyclic P) seq2 property,},

  cases defeats with z defeats,
  use z,

  unfold split_cycle_VCCR at defeats,
  cases defeats with m defeats,
  intro f,
  unfold margin_pos, simp_rw margin_eq_margin f _inst_1,
  use m,

  push_neg at defeats,
  intros c z_mem x_mem,
  specialize defeats c.reverse, 
  specialize defeats (list.mem_reverse.mpr x_mem), 
  specialize defeats (list.mem_reverse.mpr z_mem),
  
  rw margin_reverse_eq,
  simp_rw margin_reverse_eq,

  contrapose defeats,
  push_neg, push_neg at defeats,
  exact cycle_reverse_in_reverse_relation (λ (a b : X), margin P x z ≤ margin P b a) c defeats,
end