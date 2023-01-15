/-
COMP2009-ACE

Exercise 02 (Predicate logic) (20)

    This exercise has 2 parts. In the 1st part you are supposed to
    formally define what certain relation bewteen humans are (like
    Father, brother-in-law etc). Here we use Lean only as a syntax  
    and type checker. 
    In the 2nd part we play logic poker again :-) but this time for
    predicate logic. 

-/

-- part 1 (10)
namespace family

-- Given the following type, predicates and relations:

constant People : Type
constants Male Female : People → Prop
-- Male x means x is male
-- Female x means x is fmeale
constant Parent : People → People → Prop
-- Parent x y means x is a parent of y
constant Married : People → People → Prop
-- Married x y means x is married to y

/-
Define the following relations (People → People → Prop) 
using the predicates and relations above:

- Father x y = x is the father of y
- Brother x y = x is the brother of y
- Grandmother x y = x is the grandmother of y
- FatherInLaw x y = x is the father-in-law of y
- SisterInLaw x y = x is the sister in law of y
- Uncle x y = x is the uncle of y

If you are not sure about the definition of these terms, check them 
in wikipedia. If there is more than one option choose one.
-/

/- As an example: here is the definition of Father: -/

def Father (x y : People) : Prop
  := Parent x y ∧ Male x

-- add your definitions here!

end family

-- part 2 (10)
namespace poker
/-
   We play the game of logic poker - but this time with predicate logic :-)

    You have to classify the propositions into
    a) provable intuitionistically (i.e. in plain lean)
    b) provable classically (using em : P ∨ ¬ P or raa : ¬¬ P → P).
    c) not provable classically.
    and then you have to prove the propositions in a) and b) accordingly.

    Here is how you score:
    We start with 10 points :-)
    For any proposition which you didn't classify correctly (or not at all)
    you loose 1 point. :-(
    For any proposition which is provable but you didn't prove you loose
    1 point. :-(
    We stop subtracting points at 0. :-)

    Write the classification as a comment using -- after the proposition.

    You are only allowed to use the tactics introduced in the lecture
    (i.e. assume, exact, apply, constructor, cases, left, right, have, 
    trivial, existsi, reflexivity, rewrite)

    Please only use the tactics in the way indicated in the script,
    otherwise you may lose upto 2 style points. 

    For propositions classified into c) just keep "sorry," as the proof.
-/

variable A : Type
variables PP QQ : A → Prop
variables RR : A → A → Prop
variables P Q R : Prop

open classical

theorem raa : ¬ ¬ P → P := 
begin
  assume nnp,
  cases (em P) with p np,
    exact p,
    have f : false,
      apply nnp,
      exact np,
    cases f,
end

theorem ex01 : (∀ x:A, ∃ y : A , RR x y) → (∃ y : A, ∀ x : A, RR x y) :=
begin 
    -- Not provable (c)
    sorry,
end

theorem ex02 :  (∃ y : A, ∀ x : A, RR x y) → (∀ x:A, ∃ y : A , RR x y) :=
begin 
    assume a b,
    /-
        a : ∃ y : A, ∀ x : A, RR x y 
        b : A
        ⊢  ∃ y : A , RR x y
    -/    
    cases a with c d,
    /-
        b c : A
        d : ∀ x : A, RR x y 
        ⊢  ∃ y : A , RR x y
    -/
    existsi c,
    /-
        b c : A
        d : ∀ x : A, RR x y
        ⊢  RR x c
    -/
    apply d,
    /-
        No goals
    -/
end

theorem ex03 : ∀ x y : A, x = y → RR x y → RR x x :=
begin 
    assume x y a,
    /-
        x y : A
        a : x = y
        ⊢ RR x y → RR x x
    -/ 
    rewrite a,
    /-
        x y : A
        a : x = y
        ⊢ RR y y → RR y y
    -/ 
    assume b,
    /-
        x y : A
        a : x = y
        b : RR y y
        ⊢ RR y y
    -/ 
    exact b,
    /-
        No goals
    -/
end

theorem ex04 : ∀ x y z : A, x ≠ y → x ≠ z → y ≠ z :=
begin 
    sorry
    -- Not provable
end

theorem ex05 : ∀ x y z : A, x = y → x ≠ z → y ≠ z :=
begin 
    assume x y z xy xz yz,
    /-
        x y z : A
        xy : x = y
        xz : x ≠ z
        yz : y = z
        ⊢ false
    -/
    apply xz,
    /-
        x y z : A
        xy : x = y
        xz : x ≠ z
        yz : y = z
        ⊢ x = z
    -/
    rewrite xy,
    /-
        x y z : A
        xy : x = y
        xz : x ≠ z
        yz : y = z
        ⊢ y = z
    -/
    exact yz,
    /-
        No goals
    -/
end

theorem ex06 : ∀ x y z : A, x ≠ y → (x ≠ z ∨ y ≠ z) :=
begin 
    assume x y z xy,
    /-
        x y z : A
        xy : x ≠ y
        ⊢  x ≠ z ∨ y ≠ z
    -/
    cases em (y = z) with h nh,
    /-
        (Case 1)
        x y z : A
        xy : x ≠ y
        h : y = z
        ⊢  x ≠ z ∨ y ≠ z

        (Case 2)
        x y z : A
        xy : x ≠ y
        h : y ≠ z
        ⊢  x ≠ z ∨ y ≠ z
    -/
    left,
    /-
        (Case 1)
        x y z : A
        xy : x ≠ y
        h : y = z
        ⊢  x ≠ z

        (Case 2)
        x y z : A
        xy : x ≠ y
        h : y ≠ z
        ⊢  x ≠ z ∨ y ≠ z
    -/
    rewrite← h,
    /-
        (Case 1)
        x y z : A
        xy : x ≠ y
        h : y = z
        ⊢  x ≠ y

        (Case 2)
        x y z : A
        xy : x ≠ y
        h : y ≠ z
        ⊢  x ≠ z ∨ y ≠ z
    -/
    exact xy,
    /-
        Gets rid of Case 1
    -/
    right,
    /-
         (Case 2)
        x y z : A
        xy : x ≠ y
        h : y ≠ z
        ⊢ y ≠ z 
    -/
    exact nh,
    /-
        No goals (Gets rid of Case 2)
    -/
end

theorem ex07 : ¬ ¬ (∀ x : A, PP x) → ∀ x : A, ¬ ¬ PP x :=
begin 
    assume x y z,
    /-
        x : ¬ ¬ ∀ x : A, PP x
        y : A
        z : ¬PP x
        ⊢   false
    -/
    apply x,
    /-
        x : ¬ ¬ ∀ x : A, PP x
        y : A
        z : ¬PP x
        ⊢  ¬ ∀ x : A, PP x
    -/
    assume a,
    /-
        x : ¬ ¬ ∀ x : A, PP x
        y : A
        z : ¬PP x
        a : ∀ x : A, PP x
        ⊢  false
    -/
    apply z,
    /-
        x : ¬ ¬ ∀ x : A, PP x
        y : A
        z : ¬PP x
        a : ∀ x : A, PP x
        ⊢  PP x
    -/ 
    apply a, 
    /-
        No goals
    -/
end

theorem ex08 : (∀ x : A, ¬ ¬ PP x) → ¬ ¬ ∀ x : A, PP x :=
begin 
    assume x y,
    /-
        x : ∀ x : A, ¬ ¬ PP x
        y : ¬ ∀ x : A, PP x
        ⊢ false
    -/
    apply y
    /-
        x : ∀ x : A, ¬ ¬ PP x
        y : ¬ ∀ x : A, PP x
        ⊢ ∀ x : A, PP x
    -/
    assume z,
    /-
        x : ∀ x : A, ¬ ¬ PP x
        y : ¬ ∀ x : A, PP x
        z : A
        ⊢ PP x
    -/   
    apply raa,
    /-
        x : ∀ x : A, ¬ ¬ PP x
        y : ¬ ∀ x : A, PP x
        z : A
        ⊢ ¬¬ PP x
    -/   
    apply x,
    /-
        No goals
    -/
end

theorem ex09 : (∃ x : A, true) → (∃ x:A, PP x) → ∀ x : A,PP x :=
begin 
    sorry,
end

theorem ex10 : (∃ x : A, true) → (∃ x:A, PP x → ∀ x : A,PP x) :=
begin 
  sorry
end

end poker

