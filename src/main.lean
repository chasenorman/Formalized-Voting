import set_theory.cardinal
import data.finset.basic
import data.stream.basic
import tactic
import cycles

open_locale classical
noncomputable theory

-- Definition 1: Prof V X represents the set of (V, X)-profiles
def Prof : Type → Type → Type := λ (V X : Type), V → X → X → Prop

-- Definition 2: Given a profile P and x, y ∈ X(P)
-- we say that x is majority preferred to y in P if
-- more voters rank x above y than rank y above x.
def majority_preferred {V X : Type} : Prof V X → X → X → Prop := λ P x y,
cardinal.mk {v : V // P v x y} > cardinal.mk {v : V // P v y x}

-- Definition 3: Given a profile P and x₁, x₂ ∈ X(P), 
-- the margin of x₁ over x₂ in P, denoted Marginₚ(x₁, x₂), is 
-- |{i ∈ V (P) | x₁Pᵢx₂}| − |{i ∈ V (P) | x₂Pᵢx₁}|.
def margin {V X : Type} [fintype V] : Prof V X → X → X → ℤ := 
    λ P x₁ x₂, ↑(finset.univ.filter (λ v, P v x₁ x₂)).card 
    - ↑(finset.univ.filter (λ v, P v x₂ x₁)).card

-- The property of skew-symmetry takes in a function 
-- and outputs the proposition stating that the 
-- skew-symmetry equation holds for all pairs:
def skew_symmetric {X : Type} : (X → X → ℤ) → Prop := 
    λ M, ∀ x y, M x y = - M y x.

-- Proof that Marginₚ is skew-symmetric for any profile P.
lemma margin_skew_symmetric {V X : Type} (P : Prof V X) [fintype V] : skew_symmetric (margin P) :=
begin
    unfold margin,
    obviously,
end

-- We say that x is a majority winner in P if the number of voters 
-- who rank x (and only x) in first place is greater than the number 
-- of voters who do not rank x in first place.
def majority_winner {V X : Type} (P : Prof V X) (x : X) : Prop := 
    cardinal.mk {v : V // ∀ y ≠ x, P v x y} > cardinal.mk {v : V // ∃ y ≠ x, P v y x}

-- Definition 5: Let SCC be a function that assigns 
-- to each pair (V, X) the set of all (V, X)-SCCs.
def SCC := λ (V X : Type), Prof V X → set X

def universal_domain_SCC {V X : Type} (F : SCC V X) : Prop := 
    ∀ P : Prof V X, F P ≠ ∅

-- Definition 6: A variable-election social choice correspondence (VSCC) 
-- is a function F that assigns to each pair (V, X) a (V,X)-SCC. 
def VSCC : Type 1 := Π (V X : Type), SCC V X.

def finite_universal_domain_VSCC (F : VSCC) : Prop :=
    ∀ V X [inhabited V] [inhabited X] [fintype V] [fintype X], universal_domain_SCC (F V X)

-- A collective choice rule for (V, X), or (V, X)-CCR, is 
-- a function f : Prof(V, X) → B(X). Let CCR be a function 
-- that assigns to each pair (V, X) of the set of all (V,X)-CCRs.
def CCR := λ (V X : Type), Prof V X → X → X → Prop

-- Definition 8: A variable-election collective choice rule (VCCR) 
-- is a function that assigns to each pair (V, X) a (V, X)-CCR.
def VCCR := Π (V X : Type), CCR V X

-- Definition 9: Given an asymmetric VCCR F, we define the induced VSCC F* 
-- such that for any V, X, and (V, X)-profile P, we have
-- F*(V,X)(P) = {x ∈ X(P) | ∀y ∈ X(P), (y, x) ∉ F(V, X)(P)}.
def max_el_VSCC : VCCR → VSCC := λ f V X P, {x | ∀ y : X, ¬ f V X P y x}

lemma max_el_VSCC_ineq {first second : ℕ} : first < second → (second - 1).succ = second := by omega
lemma max_el_VSCC_ineq2 (first second i : ℕ) : i < second - first - 1 → (first + (second - first - 1 - (i + 1))).succ = (first + (second - first - 1 - i)) := by omega

lemma false_of_sequence_acyclic_vccr {V X : Type} [fintype X] {F : VCCR} {P : Prof V X} (p₂ : acyclic (F V X P)) (seq : stream X) (property : ∀ x : ℕ, F V X P (seq.nth x.succ) (seq.nth x)) : false := 
begin
    have noninjective := not_injective_infinite_fintype seq,
    simp at noninjective,
    cases noninjective with first noninjective, 
    cases noninjective with second noninjective,
    cases noninjective with noninjective ne,
    wlog h : first < second using [first second, second first],
    exact ne_iff_lt_or_gt.mp ne,
    let l := (list.drop first (stream.take seq second)).reverse,
    have not_acyclic : ¬ acyclic (F V X P),
    unfold acyclic,
    push_neg,
    use l,
    have e : l ≠ list.nil,
    refine list.ne_nil_of_length_pos _,
    rw list.length_reverse,
    rw list.length_drop,
    rw stream.length_take,
    omega,
    use e,
    refine list.chain_iff_nth_le.mpr _,
    split,
        {intro _,
        have eq1 : (l.last e) = seq second,
        rw ←noninjective,
        rw last_reverse,
        rw list.nth_le_drop',
        rw nth_take,
        rw nat.add_zero,
        rw nat.add_zero, 
        exact h,
        have lengths_equal : (list.drop first (seq.take second)).length = l.length,
        rw list.length_reverse,
        rw lengths_equal,
        exact gt.lt h_1,
        rw eq1,
        have eq2 : (l.nth_le 0 h_1) = seq (second - 1),
        simp_rw [nth_reverse, list.length_drop, stream.length_take, list.nth_le_drop'],
        rw nth_take,
        congr,
        omega, 
        omega,
        rw eq2,
        specialize property (second - 1),
        rw (max_el_VSCC_ineq h) at property,
        exact property,},
    
        {intro i, intro i_bound,
        simp_rw [nth_reverse, list.length_drop, stream.length_take, list.nth_le_drop'],
        rw nth_take, rw nth_take,
        specialize property (first + (second - first - 1 - (i + 1))),
        simp_rw [list.length_reverse, list.length_drop, stream.length_take] at i_bound,
        rw (max_el_VSCC_ineq2 first second i i_bound) at property,
        exact property,
        omega, omega,
        },

    exact not_acyclic p₂,
end

def max_el_VSCC_defined {V X : Type} (F : VCCR) (P : Prof V X) (p₁ : acyclic (F V X P)) [fintype X] [inhabited X] : ((max_el_VSCC F) V X P).nonempty := 
begin
    change ∃ x, ∀ (y : X), ¬ F V X P y x,
    by_contradiction,
    push_neg at h,
    let seq := stream.iterate (λ b, classical.some (h b)) _inst_2.default,
    have property : ∀ x : ℕ, F V X P (seq.nth x.succ) (seq.nth x),
    intro x,
    specialize h (seq.nth x),
    change F V X P (classical.some h) (seq.nth x),
    exact classical.some_spec h,
    exact false_of_sequence_acyclic_vccr p₁ seq property,
end

-- Any acyclic VCCR induces a VSCC satisfying (finite) universal domain
theorem max_el_VSCC_universal_domain (F : VCCR)
(a : ∀ V X [inhabited V] [inhabited X] [fintype V] [fintype X] (P : Prof V X), acyclic (F V X P)) :
finite_universal_domain_VSCC (max_el_VSCC F) := 
begin
    intros V' X',
    introsI _inst_1' _inst_2' _inst_3' _inst_4',
    specialize a V', specialize a X', 
    intro P,
    specialize a P,
    rw set.ne_empty_iff_nonempty,
    exact max_el_VSCC_defined F P a,
end


variables {V X : Type}

def asymmetric (Q : X → X → Prop) : Prop := ∀ x y, Q x y → ¬ Q y x

class profile_irreflexive {V X : Type} (P : Prof V X) := (irreflexive: ∀ v, irreflexive (P v))
class profile_asymmetric {V X : Type} (P : Prof V X) := (asymmetric: ∀ v, asymmetric (P v))
class profile_transitive {V X : Type} (P : Prof V X) := (transitive: ∀ v, transitive (P v))
class profile_trichotomous {V X : Type} (P : Prof V X) := (trichotomous: ∀ v a b, P v a b ∨ a = b ∨ P v b a)


def irreflexive_of_asymmetric (P : Prof V X) [profile_asymmetric P] : profile_irreflexive P :=
begin
    split,
    intros v x,
    have p := _inst_1.asymmetric,
    specialize p v,
    specialize p x, specialize p x,
    by_cases P v x x,
    exact p h,
    exact h,
end

def antisymmetric : (X → X → ℤ) → Prop := λ P, ∀ x y, P x y = - P y x

lemma margin_antisymmetric (P : Prof V X) [fintype V] : antisymmetric (margin P) :=
begin
    unfold margin,
    obviously,
end

def margin_pos [fintype V] : Prof V X → X → X → Prop := λ P x y, 0 < (margin P) x y

lemma margin_eq_margin (x y : fintype V) : ∀ P (a b : X), @margin V X x P a b = @margin V X y P a b :=
begin
    intros P a b,
    congr,
end 

lemma self_margin_zero [fintype V] (x : X) (P : Prof V X): margin P x x = 0 := 
begin 
    unfold margin,
    simp,
end 

lemma ne_of_margin_pos [fintype V] {P : Prof V X} {x y : X} (a : margin_pos P x y) : x ≠ y :=
begin
    by_contradiction,
    push_neg at h,
    rw h at a,
    unfold margin_pos at a,
    rw self_margin_zero at a,
    exact int.lt_irrefl 0 a,
end
