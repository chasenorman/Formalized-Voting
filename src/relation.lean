import tactic

variables {X : Type}

def P (Q : X → X → Prop) : X → X → Prop := λ x y, Q x y ∧ ¬ Q y x

-- uniformily defines indifference for P and R relations
def I (Q : X → X → Prop) : X → X → Prop := λ x y, x = y ∨ (Q x y ∧ Q y x)

def N (Q : X → X → Prop) : X → X → Prop := λ x y, ¬x = y ∧ ¬ Q x y ∧ ¬ Q y x

lemma P_asymmetric (Q : X → X → Prop) {x y : X} : (P Q) x y → ¬ (P Q) y x :=
begin
  intros ᾰ ᾰ_1, cases ᾰ_1, cases ᾰ, solve_by_elim,
end

lemma P_irrefl (Q : X → X → Prop) {x : X} : ¬ (P Q) x x :=
begin
  intros ᾰ, cases ᾰ, solve_by_elim,
end

lemma I_refl (Q : X → X → Prop) {x : X} : (I Q) x x :=
begin
  unfold I,
  have e : x = x := by refl,
  use e,
end

lemma N_irrefl (Q : X → X → Prop) {x : X} : ¬(N Q) x x :=
begin
  unfold N,
  push_neg,
  intro n,
  exfalso,
  have e : x = x := by refl,
  exact n e,
end

