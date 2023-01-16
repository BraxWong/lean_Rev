/-
COMP2009 Tutorial 2
-/

variables P Q R : Prop

/-
What is a logic?
A particular system or codification of the principles of proof and inference.
* Propositional logic - a formal system where formulae are built by joining
  propositions using logical connectives.
* Classical logic - logic based on truth value (uses truth tables).
* Intuitionistic logic - logic based on evidence. 
* Predicate logic - extends propositional logic and will be covered next week. 

Classical Logic = Intuitionistic Logic + Excluded Middle (em P : P ∨ ¬ P)

It turns out that excluded middle is equivalent to another law, double
negation elimination/reductio ad absurdum (raa P : ¬ ¬ P → P).

The basic tactics seen so far in Lean have all been intuitionistic. In order
to prove classical logic formulae, we have to tell Lean we want to work in
classical logic and access EM by doing the following.
-/

open classical

-- This makes the following available.

-- #check (em P)

--------------------------------------------------------------------------------
-- PART I : EM & RAA

-- Proof that EM (P ∨ ¬ P) implies RAA (¬ ¬ P → P)

theorem raa : ¬ ¬ P → P := 
begin
    assume nnp,
    /-
        nnp : ¬ ¬ P
        ⊢ P
    -/
    cases (em P) with p np,
    /-
        (Case 1)
        nnp : ¬ ¬ P
        p : P
        ⊢ P

        (Case 2)
        nnp : ¬ ¬ P
        p : ¬ P
        ⊢ P
    -/
    exact p,
    /-
        Gets rid of Case 1
    -/
    have f : false,
    /-
        (Case 2.1)
        nnp : ¬ ¬ P
        p : ¬ P
        ⊢ false

        (Case 2.2)
        nnp : ¬ ¬ P
        p : ¬ P
        f : false
        ⊢ P
    -/
    apply nnp,
    /-
        (Case 2.1)
        nnp : ¬ ¬ P
        p : ¬ P
        ⊢ ¬ P

        (Case 2.2)
        nnp : ¬ ¬ P
        p : ¬ P
        f : false
        ⊢ P
    -/
    exact np,
    /-
        Gets rid of Case 2.1
    -/
    cases f,
    /-
        No goals (Gets rid of Case 2.2)
    -/
end

-- #check raa

-- Proof that RAA (¬ ¬ P → P) implies EM (P ∨ ¬ P) 
-- (requires an auxiliary proof)

theorem nn_em : ¬ ¬ (P ∨ ¬ P) :=
begin   
    assume npnp,
    /-
        npnp : ¬ (P ∨ ¬ P)
        ⊢ false
    -/   
    apply npnp,
    /-
        npnp : ¬ (P ∨ ¬ P)
        ⊢ P ∨ ¬ P
    -/
    right,
    /-
        npnp : ¬ (P ∨ ¬ P)
        ⊢ ¬ P
    -/
    assume p,
    /-
        npnp : ¬ (P ∨ ¬ P)
        p : P
        ⊢ false
    -/
    apply npnp,
    /-
        npnp : ¬ (P ∨ ¬ P)
        p : P
        ⊢ P ∨ ¬ P
    -/
    left,
    /-
        npnp : ¬ (P ∨ ¬ P)
        p : P
        ⊢ P 
    -/
    exact p,
    /-
        No goals
    -/
end  

theorem my_em : P ∨ ¬ P :=
begin
  apply raa (P ∨ ¬ P),
  apply nn_em,
end 

-- Any classical logic formula can be proved by assuming either one
-- of EM or RAA.

------------------------------------------------------------------------------
-- PART II: Examples

/-
3 possible cases: 
* A) provable intuitionistically
* B) provable classically
* C) not provable 
-/     

-- A) Intuitionistic
theorem example_1 : ((P ∨ Q) ∧ ¬ P) → Q :=
begin
    assume hyp,
    /-
        hyp : P ∨ Q ∧ ¬ P
        ⊢ Q
    -/
    cases hyp with pq np,
    /-
        pq : P ∨ Q 
        np : ¬ P
        ⊢ Q
    -/
    cases pq with p q,
    /-
        (Case P)
        p : P 
        np : ¬ P
        ⊢ Q

       (Case Q)
        q : Q 
        np : ¬ P
        ⊢ Q 
    -/
    have f : false,
    /-
        (Case P.1)
        p : P 
        np : ¬ P
        ⊢ false

        (Case P.2)
        p : P 
        np : ¬ P
        f : false
        ⊢ Q

       (Case Q)
        q : Q 
        np : ¬ P
        ⊢ Q 
    -/
    apply np,
    /-
        (Case P.1)
        p : P 
        np : ¬ P
        ⊢ P

        (Case P.2)
        p : P 
        np : ¬ P
        f : false
        ⊢ Q

       (Case Q)
        q : Q 
        np : ¬ P
        ⊢ Q 
    -/
    exact p,
    /-
        Gets rid of Case P.1
    -/ 
    cases f,
    /-
        Gets rid of Case P.2
    -/
    exact q,
    /-
        No goals (Gets is of Case Q)
    -/
end  
-- B) Classical
theorem example_2_em : (¬ P → Q) → (¬ Q → P) :=
-- contrapositive: (P → Q) → (¬ Q → ¬ P)
begin
    assume np2q,
    assume nq,
    /-
        np2q : ¬ P → Q
        nq : ¬ Q
        ⊢ P
    -/
    cases (em P) with p np,
    /-
        (Case p)
        np2q : ¬ P → Q
        nq : ¬ Q
        p : P
        ⊢ P

        (Case np)
        np2q : ¬ P → Q
        nq : ¬ Q
        np : ¬ P
        ⊢ P
    -/
    exact p,
    /-
        Gets rid of Case p
    -/
    have f : false,
    /-
        (Case np, f.1)
        np2q : ¬ P → Q
        nq : ¬ Q
        np : ¬ P
        ⊢ false

        (Case np, f.2)
        np2q : ¬ P → Q
        nq : ¬ Q
        np : ¬ P
        f : false
        ⊢ P
    -/
    apply nq,
    /-
        (Case np, f.1)
        np2q : ¬ P → Q
        nq : ¬ Q
        np : ¬ P
        ⊢ Q

        (Case np, f.2)
        np2q : ¬ P → Q
        nq : ¬ Q
        np : ¬ P
        f : false
        ⊢ P
    -/
    apply np2q,
    /-
        (Case np, f.1)
        np2q : ¬ P → Q
        nq : ¬ Q
        np : ¬ P
        ⊢ ¬ P

        (Case np, f.2)
        np2q : ¬ P → Q
        nq : ¬ Q
        np : ¬ P
        f : false
        ⊢ P
    -/
    exact np,
    /-
        Gets rid of Case np
    -/
    cases f,
    /-
        No goals (Gets rid of Case np, f.2)
    -/
end 

theorem example_2_raa : (¬ P → Q) → (¬ Q → P) :=
begin
    assume np2q,
    assume nq,
    /-
        np2q : ¬ P → Q  
        nq : ¬ Q
        ⊢ P
    -/
    apply raa,
    /-
        np2q : ¬ P → Q  
        nq : ¬ Q
        ⊢ ¬¬ P
    -/
    assume np,
    /-
        np2q : ¬ P → Q  
        nq : ¬ Q
        np : ¬ P 
        ⊢ false
    -/
    apply nq,
    /-
        np2q : ¬ P → Q  
        nq : ¬ Q
        np : ¬ P 
        ⊢ Q
    -/
    apply np2q,
    /-
        np2q : ¬ P → Q  
        nq : ¬ Q
        np : ¬ P 
        ⊢ ¬ P
    -/
    exact np,
    /-
        No goals
    -/
end

/-
P | ¬ P | P ∨ ¬ P | ¬ (P ∨ ¬ P)
T |  F  |   T     |    F
F |  T  |   T     |    F
-/

-- C) Not provable
theorem example_3 : ¬ (P ∨ ¬ P) :=
begin
  sorry,
end

-- B) Classical
theorem example_4_em : (¬ P → P) → P :=
begin
    assume np2p,
    /-
        np2p : ¬ P → P
        ⊢ P
    -/
    cases (em P) with p np,
    /-
        (Case p)
        np2p : ¬ P → P
        p : P
        ⊢ P

        (Case np)
        np2p : ¬ P → P
        np : ¬P
        ⊢ P
    -/
    exact p,
    /-
        Gets rid of Case p
    -/
    apply np2p,
    /-
        (Case np)
        np2p : ¬ P → P
        np : ¬P
        ⊢ ¬P
    -/
    exact np,
    /-
        No goals (Gets rid of Case np)
    -/
end  

theorem example_4_raa : (¬ P → P) → P :=
begin
    assume np2p,
    /-
        np2p : ¬ P → P
        ⊢ P
    -/
    apply raa,
    /-
        np2p : ¬ P → P
        ⊢ ¬¬ P
    -/
    assume np,
    /-
        np2p : ¬ P → P
        np : ¬ P
        ⊢ false
    -/
    apply np,
    /-
        np2p : ¬ P → P
        np : ¬ P
        ⊢ P 
    -/
    apply np2p,
    /-
        np2p : ¬ P → P
        np : ¬ P
        ⊢ ¬ P 
    -/
    exact np,
    /-
        No goals
    -/
end

/-
Tips:
* using truth tables tells us whether something is provable or not, but does 
  not tell us whether it is provable intuitionistically or classically 
* when trying to prove something intuitionistically, think of witnesses/evidence
  e.g. ¬ (P ∧ Q) → (¬ P ∨ ¬ Q) vs (¬ P ∨ ¬ Q) → ¬ (P ∧ Q)
  have f : P ∧ Q → false
  want either g : P → false or h : Q → false
  not provable intuitionistically
  --
  have either f : P → false or g : Q → false
  want h : P ∧ Q → false
  provable intuitionistically
-/
