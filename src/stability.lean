import main
import split_cycle

open_locale classical

variables {V X : Type}

def minus_candidate (P : Prof V X) (b : X) : Prof V {x : X // x ≠ b} := λ v x y, P v x.val y.val

def strong_stability [fintype V] (F : VSCC) (P : Prof V X) : Prop := 
  ∀ (a b : X) (e : a ≠ b), 0 ≤ margin P a b → (⟨a, e⟩ : {x : X // x ≠ b}) ∈ F V {x : X // x ≠ b} (minus_candidate P b) → a ∈ F V X P

lemma margin_eq_margin_minus_candidate [fintype V] {P : Prof V X} (b : X) {x y : X} (h : x ≠ b) (e : y ≠ b) : 
  margin (minus_candidate P b) ⟨x, h⟩ ⟨y, e⟩ = margin P x y := 
begin
  obviously,
end

theorem split_cycle_strong_stability [fintype V] (P : Prof V X) : strong_stability split_cycle P :=
begin
  unfold strong_stability,
  intros a b e m w y,
  unfold split_cycle at *, unfold max_el_VSCC at *,
  simp at *,
  unfold split_cycle_VCCR, unfold split_cycle_CCR,
  simp at *,
  use _inst_1,
  --intro p,
  by_cases y ≠ b,
    {specialize w y, specialize w h,
    unfold split_cycle_VCCR at w, unfold split_cycle_CCR at w,
    simp at w,
    cases w with i2 w,
    intro m2,
    unfold margin_pos at m2,
    rw ←(margin_eq_margin_minus_candidate b h e) at m2,
    change margin_pos (minus_candidate P b) ⟨y, h⟩ ⟨a, e⟩ at m2,
    unfold margin_pos at w,
    rw margin_eq_margin i2 _inst_1 at w,
    specialize w m2,
    cases w with c w,
    cases w with y_mem w,
    cases w with a_mem w,
    use (c.map subtype.val),
    simp,
    use h, exact y_mem,
    use e, exact a_mem,
    rw ←margin_eq_margin_minus_candidate b h e,
    unfold cycle at *,
    cases w with n w,
    split,
    work_on_goal 1
      {by_contradiction, push_neg at h, exact n (list.map_eq_nil.mp h),},
    rw list.last_map subtype.val n,
    refine list.chain_map_of_chain subtype.val _ w,
    obviously,
    rw margin_eq_margin i2 _inst_1 at ᾰ,
    obviously,},
  push_neg at h,
  rw h,
  intro m2,
  rw margin_antisymmetric at m,
  exfalso,
  simp at m,
  have o : ∀ (n : ℤ), n ≤ 0 → ¬ 0 < n := by omega,
  exact (o (margin P b a) m) m2,
end
