import set_theory.cardinal
import data.finset.basic
import data.stream.basic
import tactic

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

-- Proof that Marginₚ is skew-symmetric for any Prof P.
lemma margin_skew_symmetric {V X : Type} (P : Prof V X) [fintype V] : skew_symmetric (margin P) :=
begin
    unfold margin,
    obviously,
end

-- Definition 4: Given a profile P and x ∈ X(P), we say that x is 
-- a Condorcet winner in P if for all y ∈ X(P) with y ≠ x, 
-- x is majority preferred to y in P.
def condorcet_winner {V X : Type} (P : Prof V X) (x : X) : Prop := 
    ∀ y ≠ x, majority_preferred P x y

-- We say that x is a majority winner in P if the number of voters 
-- who rank x (and only x) in first place is greater than the number 
-- of voters who do not rank x in first place.
def majority_winner {V X : Type} (P : Prof V X) (x : X) : Prop := 
    cardinal.mk {v : V // ∀ y ≠ x, P v x y} > cardinal.mk {v : V // ∃ y ≠ x, P v y x}

-- Proof that a majority winner is a Condorcet winner.
lemma condorcet_of_majority_winner {V X : Type} (P : Prof V X) [fintype V] (x : X) : majority_winner P x → condorcet_winner P x :=
begin
    intros majority z z_ne_x, 
    have imp1 : ∀ v, (∀ y ≠ x, P v x y) → P v x z := by finish,
    refine lt_of_lt_of_le _ (cardinal.mk_subtype_mono imp1), 
    have imp2 : ∀ v, P v z x → (∃ y ≠ x, P v y x) := by finish,
    apply lt_of_le_of_lt (cardinal.mk_subtype_mono imp2),
    exact majority,
end

-- Definition 5: Let SCC be a function that assigns 
-- to each pair (V, X) the set of all (V, X)-SCCs.
def SCC := λ (V X : Type), Prof V X → set X

def universal_domain_SCC {V X : Type} (F : SCC V X) : Prop := 
    ∀ P : Prof V X, F P ≠ ∅

-- Example 1: Given a (V, X)-profile P, if there is a Condorcet winner, 
-- then output the set of all Condorcet winners (which will be a singleton),
-- and otherwise output all candidates in X.
def condorcet_SCC {V X : Type} : SCC V X := λ P,
    {x : X | condorcet_winner P x ∨ (¬∃ y, condorcet_winner P y)}

-- Definition 6: A variable-election social choice correspondence (VSCC) 
-- is a function F that assigns to each pair (V, X) a (V,X)-SCC. 
def VSCC : Type 1 := Π (V X : Type), SCC V X.

def finite_universal_domain_VSCC (F : VSCC) : Prop :=
    ∀ V X [inhabited V] [inhabited X] [fintype V] [fintype X], universal_domain_SCC (F V X)

-- Example 2
def condorcet_VSCC : VSCC := λ V X, condorcet_SCC

-- A collective choice rule for (V, X), or (V, X)-CCR, is 
-- a function f : Prof(V, X) → B(X). Let CCR be a function 
-- that assigns to each pair (V, X) of the set of all (V,X)-CCRs.
def CCR := λ (V X : Type), Prof V X → X → X → Prop

-- cycle takes in a binary relation R and a list c of
-- elements of X and  outputs the proposition stating that 
-- (i) there is a proof e that c is not the empty list, and 
-- (ii) c is a cycle in R.
def cycle {X: Type} := λ (R : X → X → Prop) (c : list X),
    ∃ (e : c ≠ list.nil), list.chain R (c.last e) c

-- Example 3: A candidate x defeats a candidate y in P 
-- just in case the margin of x over y is (i) positive and 
-- (ii) greater than the weakest margin in each majority cycle containing x and y. 
def split_cycle_CCR {V X : Type} : CCR V X :=
    λ (P : Prof V X) (x y : X), ∀ [f: fintype V],
    0 < @margin V X f P x y ∧
    ¬ (∃ (c : list X), x ∈ c ∧ y ∈ c ∧
    cycle (λ a b, @margin V X f P x y ≤ @margin V X f P a b) c)

-- Definition 8: A variable-election collective choice rule (VCCR) 
-- is a function that assigns to each pair (V, X) a (V, X)-CCR.
def VCCR := Π (V X : Type), CCR V X

-- Example 4
def split_cycle_VCCR : VCCR := λ V X, split_cycle_CCR

-- Definition 9: Given an asymmetric VCCR F, we define the induced VSCC F* 
-- such that for any V, X, and (V, X)-profile P, we have
-- F*(V,X)(P) = {x ∈ X(P) | ∀y ∈ X(P), (y, x) ∉ F(V, X)(P)}.
def max_el_VSCC : VCCR → VSCC := λ f V X P, {x | ∀ y : X, ¬ f V X P y x}

-- Example 5: The Split Cycle voting method is 
-- the induced VSCC from the Split Cycle VCCR
def split_cycle : VSCC := max_el_VSCC split_cycle_VCCR

def acyclic {X : Type} : (X → X → Prop) → Prop := 
    λ Q, ∀ (c : list X), ¬ cycle Q c

-- Any acyclic VCCR induces a VSCC satisfying (finite) universal domain
-- the proof for the following theorem can be found in src/main.lean
theorem max_el_VSCC_universal_domain (F : VCCR)
(a : ∀ V X [inhabited V] [inhabited X] [fintype V] [fintype X] (P : Prof V X), acyclic (F V X P)) :
finite_universal_domain_VSCC (max_el_VSCC F) := sorry

-- Converts a walk to a path 
noncomputable def to_path {X : Type} : list X → list X
| [] := []
| (u :: p) := let p' := to_path p in
    if u ∈ p' then (p'.drop (p'.index_of u)) else (u :: p')

-- Given a particular candidate c, we say that a nonempty set D of candidates 
-- (not containing c) is a set of clones of c if D ∪ {c} is a set of clones. 
def clones {V X : Type} (P : Prof V X) (c : X) (D : set {x : X // x ≠ c}) : 
    Prop := D.nonempty ∧ (∀ (c' ∈ D) (x : {x : X // x ≠ c}) (i : V), 
    x ∈ D → ((P i c x ↔ P i c' x) ∧ (P i x c ↔ P i x c')))

-- minus_candidate takes in a Prof P for V and X, as well as 
-- a candidate b from X, and outputs the Prof for V and {x : X // x ̸= b} 
-- that agrees with P on how every voter ranks the candidates other than b.
def minus_candidate {V X : Type} (P : Prof V X) (b : X) : 
    Prof V {x : X // x ≠ b} := λ v x y, P v x y

--  removing a clone from a profile should not change which non-clones win
def non_clone_choice_ind_clones {V X : Type} (P : Prof V X) (c : X) (D : set {x : X // x ≠ c}) 
    : VSCC → Prop :=  λ F, clones P c D → (∀ a : {x : X // x ≠ c}, 
    a ∉ D → (a.val ∈ (F V X P) ↔ a ∈ (F V {x : X // x ≠ c} (minus_candidate P c))))

-- we can state that Split Cycle satisfies part (i) of independence of clones as follows:
-- the proof for the following theorem can be found in src/clones.lean
theorem non_clone_choice_ind_clones_split_cycle {V X : Type} [fintype V] 
    (P : Prof V X) (c : X) (D : set {x : X // x ≠ c}) : non_clone_choice_ind_clones P c D split_cycle := sorry