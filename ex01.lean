theorem e01 : P → Q → P := 
begin
    assume p q,                      
    /- 
       p : P
       q : Q
       |- P
    -/
    exact p
    /-
        no goals
    -/
end

theorem e02 : (P → Q → R) → (P → Q) → P → R :=
begin
    assume pqr pq p,

    /-
        pqr : P -> Q -> R
        pq  : P -> Q
        p   : P
        |-  R
    -/

    apply pqr,

    /-
        (Case 1)
        pqr : P -> Q -> R
        pq  : P -> Q
        p   : P
        |-  P 

        (Case 2)
        pqr : P -> Q -> R
        pq  : P -> Q
        p   : P
        |-  Q
    -/

    exact p,

    /-
        gets rid of Case 1
    -/

    apply pq,

    /-
        pqr : P -> Q -> R
        pq  : P -> Q
        p   : P
        |-  P
    -/

    exact p,

    /-
        no goals
    -/
end    
 

theorem e03 : (P → Q) → P ∧ R → Q ∧ R :=
begin

    assume pq pnr,
    
    /-
        pq : P -> Q
        pnr : P ∧ R
        |-  Q ∧ R
    -/ 

    cases pnr with p r,
    /-
        pq : P -> Q
        p : P
        r : R
        |- Q ∧ R
    -/ 
    constructor,
    /-
        (Case 1)
        pq : P -> Q
        p : P
        r : R
        |- Q

        (Case 2)
        pq : P -> Q
        p : P
        r : R
        |- R
    -/
    apply pq,
    /-
        (Case 1)
        pq : P -> Q
        p : P
        r : R
        |- P

        (Case 2)
        pq : P -> Q
        p : P
        r : R
        |- R
    -/
    exact p,
    /-
        gets rid of Case 1
    -/
    exact r,
    /-
        no goals (gets rid of Case 2)
    -/
end



theorem e04 : (P → Q) → P ∨ R → Q ∨ R :=
begin
    assume pq por,
    /-
        pq : P -> Q
        por  : P ∨ R
        |- Q ∨ R
    -/  
    cases por with p r,
    /-
        (Case 1)
        pq : P -> Q
        p : P
        |- Q ∨ R

        (Case 2)
        pq : P -> Q
        r : R
        |- Q ∨ R
    -/ 
    left,
    /-
        (Case 1)
        pq : P -> Q
        p : P
        |- Q
    
        (Case 2)
        pq : P -> Q
        r : R
        |- Q ∨ R
    -/ 
    apply pq,
    /-
        (Case 1)
        pq : P -> Q
        p : P
        |- P
    
        (Case 2)
        pq : P -> Q
        r : R
        |- Q ∨ R
    -/ 
    exact p,
    /-
        Gets rid of Case 1
    -/
    right,
    /-
        (Case 2)
        pq : P -> Q
        r : R
        |- R
    -/
    exact r,
    /-
        No goals (Gets rid of Case 2)
    -/
end



theorem e05 : P ∨ Q → R ↔ (P → R) ∧ (Q → R) :=
begin
    constructor,
    /-
        (Case 1)
        P ∨ Q → R → (P → R) ∧ (Q → R) 
        
        (Case 2)
        (P → R) ∧ (Q → R) → P ∨ Q → R
    -/
    assume pqr,
    /-
        (Case 1)
        pqr : P ∨ Q → R 
        := (P → R) ∧ (Q → R) 
        
        (Case 2)
        (P → R) ∧ (Q → R) → P ∨ Q → R
    -/
    constructor,
     /-
        (Case 1)
        pqr : P ∨ Q → R 
        := (P → R)
        
        (Case 2)
        pqr : P ∨ Q → R 
        := (Q → R)

        (Case 3)
        (P → R) ∧ (Q → R) → P ∨ Q → R
    -/
    assume p,
     /-
        (Case 1)
        pqr : P ∨ Q → R 
        p : P
        := R
        
        (Case 2)
        pqr : P ∨ Q → R 
        := (Q → R)

        (Case 3)
        (P → R) ∧ (Q → R) → P ∨ Q → R
    -/
    apply pqr,
    /-
        (Case 1)
        pqr : P ∨ Q → R 
        p : P
        :=  P ∨ Q
        
        (Case 2)
        pqr : P ∨ Q → R 
        := (Q → R)

        (Case 3)
        (P → R) ∧ (Q → R) → P ∨ Q → R
    -/
    left,
    /-
        (Case 1)
        pqr : P ∨ Q → R 
        p : P
        :=  P
        
        (Case 2)
        pqr : P ∨ Q → R 
        := (Q → R)

        (Case 3)
        (P → R) ∧ (Q → R) → P ∨ Q → R
    -/
    exact p,
    /-
        Gets rid of Case 1
    -/
    assume q,
    /-
        (Case 2)
        pqr : P ∨ Q → R
        q : Q 
        := R

        (Case 3)
        (P → R) ∧ (Q → R) → P ∨ Q → R
    -/
    apply pqr,
    /-
       (Case 2)
       pqr : P ∨ Q → R
       q : Q 
       :=  P ∨ Q 

       (Case 3)
       (P → R) ∧ (Q → R) → P ∨ Q → R
    -/
    right,
     /-
       (Case 2)
       pqr : P ∨ Q → R
       q : Q 
       :=  Q 

       (Case 3)
       (P → R) ∧ (Q → R) → P ∨ Q → R
    -/
    exact q,
    /-
        Gets rid of Case 2
    -/
    assume prqr pq,
    /-
        (Case 3)
        prqr : (P → R) ∧ (Q → R) 
        pq :  P ∨ Q
        := R
    -/
    cases prqr with pr qr,
    /-
        (Case 3)
        pr : P → R
        qr : Q → R
        pq : P ∨ Q
        := R
    -/
    cases pq with p q,
    /-
        (Case 3)
        pr : P → R
        qr : Q → R
        p : P
        := R

        (Case 4)
        pr : P → R
        qr : Q → R
        q : Q
        := R
    -/
    apply pr,
    /-
        (Case 3)
        pr : P → R
        qr : Q → R
        p : P
        := P

        (Case 4)
        pr : P → R
        qr : Q → R
        q : Q
        := R
    -/
    exact p,
    /-
        Gets rid of Case 3
    -/
    apply qr,
    /-
        (Case 4)
        pr : P → R
        qr : Q → R
        q : Q
        := Q
    -/
    exact q,
    /-
        No goals (Gets rid of Case 4)
    -/
end

theorem e06 : P → ¬ ¬ P :=
begin
    assume p np,
    /-
        p : P
        np : ¬ P
        |- false
    -/
    apply np,
    /-
        p : P
        np : ¬ P
        |- P
    -/
    exact p,
    /-
        No goals 
    -/ 
end

theorem e07 : P ∧ true ↔ P :=
begin
    constructor,
    /-
        (Case 1)
        P ∧ true → P

        (Case 2)
        P → P ∧ true
    -/
    assume pt,
    /-
        (Case 1)
        pt : P ∧ true
        := P

        (Case 2)
        P → P ∧ true
    -/
    cases pt with p t,
     /-
        (Case 1)
        p : P
        t : true
         := P

        (Case 2)
        P → P ∧ true
    -/
    exact p,
    /-
        Gets rid of Case 1
    -/
    assume p,
    /-
        (Case 2)
        p : P
        ⊢ P ∧ true
    -/
    constructor,
    /-
        (Case 2)
        p : P
        ⊢  P

        (Case 3)
        p : P
        ⊢ true
    -/
    exact p,
    -/
        Gets rid of Case 2
    -/
    constructor,
    -/
        No goals (Gets rid of Case 3)
    -/
end

theorem e08 : P ∨ false ↔ P :=
begin
    constructor,
    /-
        (Case 1)
        P ∨ false → P
    
        (Case 2)
        P → P ∨ false
    -/
    assume pf,
    /-
        (Case 1)
        pf : P ∨ false 
        ⊢ P
    
        (Case 2)
        P → P ∨ false
    -/
    cases pf with p f,
    /-
        (Case 1)
        p: P 
        ⊢ P
    
        (Case 2)
        f : false
        ⊢ P
        
        (Case 3)
        P → P ∨ false
    -/
    exact p,
    /-
        Gets rid of Case 1
    -/
    cases f,
    /-
        Gets rid of Case 2
    -/
    assume p,
    /-
        (Case 3)
        p: P 
        ⊢ P ∨ false
    -/
    left,
    /-
        (Case 3)
        p: P 
        ⊢
    -/
    exact p,
    /-
        No goals (Gets rid of Case 3)
    -/
end

theorem e09 : P ∧ false ↔ false :=
begin
    constructor,
    /-
        (Case 1)
        P ∧ false → false

        (Case 2)
        false → P ∧ false
    -/
    assume pf,
    /-
        (Case 1)
        pf: P ∧ false 
        ⊢ false

        (Case 2)
        false → P ∧ false
    -/
    cases pf with p f,
    /-
        (Case 1)
        p : P 
        f : false 
        ⊢ false

        (Case 2)
        false → P ∧ false
    -/
    exact f,
    /-
        Gets rid of Case 1
    -/
    assume f,
    /-
       (Case 2)
       f: false 
       ⊢ P ∧ false
    -/
    constructor,
    /-
       (Case 2)
       f: false 
       ⊢ P

       (Case 3)
       f: false
       ⊢ false    
    -/
    cases f,
    -/
        Gets rid of Case 2
    -/
    exact f,
    -/
        No goals (Gets rid of Case 3)
    -/
end

theorem e10 : P ∨ true ↔ true :=
begin
    constructor,
    /-
        (Case 1)
        P ∨ true → true

        (Case 2)
        true → P ∨ true
    -/
    assume pt,
    /-
        (Case 1)
        pt: P ∨ true 
        ⊢ true

        (Case 2)
        true → P ∨ true
    -/
    cases pt with p t  
     /-
        (Case 1)
        p: P 
        ⊢ true
    
        (Case 2)
        t : true
        ⊢ true
 
        (Case 3)
        true → P ∨ true
    -/
    constructor,
    /-
        Gets rid of Case 1
    -/
    exact t,
    /-
        Gets rid of Case 2
    -/
    assume t,
    /-
        (Case 3)
        t : true 
        ⊢ P ∨ true
    -/
    right,
    /-
        (Case 3)
        t : true
        ⊢ true
    -/ 
    exact t,
    /-
        No goals (Gets rid of Case 3)
    -/
end

/-
Part 2 (10 points)
(this part relies in material only covered in the lectures 
from 14/10/22)

We play the game of logic poker :-)

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
    (i.e. assume, exact, apply, constructor, cases, left, right, have, trivial)

    Please only use the tactics in the way indicated in the script,
    otherwise you may lose upto 2 style points. 

    For propositions classified into c) just keep "sorry," as the proof.
-/

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

theorem p01 : (P → Q) → (R → P) → (R → Q) := 
begin
    assume pq rp r,
    /-
        pq : P → Q
        rp : R → P
        r : R
        ⊢ Q 
    -/
    apply pq,
    /-
        pq : P → Q
        rp : R → P
        r : R
        ⊢ P
    -/ 
    apply rp,
     /-
        pq : P → Q
        rp : R → P
        r : R
        ⊢ R
    -/ 
    exact r,
    /-
        No goals
    -/
end

theorem p02 : (P → Q) → (P → R) → (Q → R) :=
begin
  assume pq pr q,
  sorry,
end

theorem p03 : (P → Q) → (Q → R) → (P → R) :=
begin
    assume pq qr p,
    /-
        pq : P → Q
        qr : Q → R 
        p : P
        ⊢ R
    -/
    apply qr,
    /-
        pq : P → Q
        qr : Q → R 
        p : P
        ⊢ Q
    -/
    apply pq,
    /-
        pq : P → Q
        qr : Q → R 
        p : P
        ⊢ P
    -/
    exact p,
    /-
        No goals
    -/
end

theorem e04 : P → (P → Q) → P ∧ Q :=
begin
    assume p pq,
    /-
        p : P
        pq : P → Q
        ⊢  P ∧ Q
    -/
    constructor,
    /-
        (Case 1)
        p : P
        pq : P → Q
        ⊢  P

        (Case 2)
        p : P
        pq : P → Q
        ⊢  Q
    -/
    exact p,
    /-
        Gets rid of Case 1
    -/
    apply pq,
    /-
        (Case 2)
        p : P
        pq : P → Q
        ⊢  P
    -/
    exact p,
    /-
        No goals (Gets rid of Case 2)
    -/
end

theorem p05 : P ∨ Q → (P → Q) → Q :=
begin
    assume poq pq, 
    /-
        poq : P ∨ Q
        pq : P → Q
        ⊢ Q
    -/
    cases poq with p q,
    /-
        (Case 1)
        p : P
        pq : P → Q
        ⊢ Q

        (Case 2)
        q : Q
        pq : P → Q
        ⊢ Q
    -/
    apply pq,
    /-
        (Case 1)
        p : P
        pq : P → Q
        ⊢ P

         (Case 2)
        q : Q
        pq : P → Q
        ⊢ Q
    -/
    exact p,
    /-
        Gets rid of Case 1
    -/
    exact q,
    /-
        No goals (Gets rid of Case 2)
    -/
end


theorem p06 : (P → Q) → ¬ P ∨ Q :=
begin
    assume pq,  
    /-
        pq : P → Q
        ⊢ ¬ P ∨ Q
    -/
    apply raa,
    /-
        pq : P → Q
        ⊢ ¬¬ (¬ P ∨ Q)
    -/ 
    assume h,
    /-
        pq : P → Q
        h : ¬(¬P ∨ Q)
        ⊢ false
    -/ 
    apply h,
    /-
        pq : P → Q
        h : ¬(¬P ∨ Q)
        ⊢ ¬P ∨ Q
    -/
    left,
    /-
        pq : P → Q
        h : ¬(¬P ∨ Q)
        ⊢ ¬P
    -/
    assume p,
    /-
        pq : P → Q
        h : ¬(¬P ∨ Q)
        p : P
        ⊢ false
    -/
    apply h,
    /-
        pq : P → Q
        h : ¬(¬P ∨ Q)
        p : P
        ⊢ ¬P ∨ Q
    -/
    right,
    /-
        pq : P → Q
        h : ¬(¬P ∨ Q)
        p : P
        ⊢ Q
    -/
    apply pq,
    /-
        pq : P → Q
        h : ¬(¬P ∨ Q)
        p : P
        ⊢ P
    -/
    exact np,
    /-
        No goals
    -/
end


theorem p07 : (¬ P ∨ Q) → P → Q :=
begin
    assume h p,
    /-
        h : ¬ P ∨ Q
        p : P
        ⊢ Q
    -/
    cases h with np q,
    /-
        (Case 1)
        np : ¬ P
        p : P
        ⊢ Q
        (Case 2)
        q : Q
        p : P
        ⊢ Q
    -/
    have f : false,
    /-
        (Case 1)
        np : ¬ P
        p : P
        ⊢ false

        (Case 2)
        np : ¬ P
        p : P
        f : false
        ⊢ Q

        (Case 3)
        q : Q
        p : P
        ⊢ Q
    -/
    apply np,
    /-
        (Case 1)
        np : ¬ P
        p : P
        ⊢ P

        (Case 2)
        np : ¬ P
        p : P
        f : false
        ⊢ Q

        (Case 3)
        q : Q
        p : P
        ⊢ Q
    -/
    exact p,
    /-
        Gets rid of Case 1
    -/
    cases f,
    /-
        Gets rid of Case 2
    -/
    exact q,
    /-
        No goals (Gets rid of Case 3)
    -/
end


theorem p08 : ¬ (P ↔ ¬ P) :=
begin
    assume h,
    /-
        h : P ↔ ¬ P
        ⊢ false
    -/
    cases h with a b,
    /-
        (Case 1)
        a : P → ¬ P
        b : ¬ P → P
        ⊢ false
    -/    
    have np : ¬ P,
    /-
        (Case 1)
        a : P → ¬ P
        b : ¬ P → P
        ⊢ ¬ P

        (Case 2)
        a : P → ¬ P
        b : ¬ P → P
        np : ¬ P
        ⊢ false
    -/
    assume npp,
    /-
        (Case 1)
        a : P → ¬ P
        b : ¬ P → P
        npp : P
        ⊢ false

        (Case 2)
        a : P → ¬ P
        b : ¬ P → P
        np : ¬ P
        ⊢ false
    -/
    apply a,
    /-
        (Case 1)
        a : P → ¬ P
        b : ¬ P → P
        npp : P
        ⊢ P

        (Case 2)
        a : P → ¬ P
        b : ¬ P → P
        np : ¬ P
        ⊢ false
    -/
    exact npp,
    /-
        (Case 1)
        a : P → ¬ P
        b : ¬ P → P
        npp : P
        ⊢ P

        (Case 2)
        a : P → ¬ P
        b : ¬ P → P
        np : ¬ P
        ⊢ false
    -/
    exact npp,
    /-
        Gets rid of Case 1
    -/
    apply a,
    /-
        (Case 2)
        a : P → ¬ P
        b : ¬ P → P
        np : ¬ P
        ⊢ P
    -/
    apply b,
    /-
        (Case 2)
        a : P → ¬ P
        b : ¬ P → P
        np : ¬ P
        ⊢ ¬ P
    -/
    exact np,
    apply b,
    exact np,
end


theorem p09 : ¬ P ↔ ¬ ¬ ¬ P :=
begin
    constructor,
    /-
        (Case 1)
        ¬ P → ¬ ¬ ¬ P
        
        (Case 2)
        ¬ ¬ ¬ P → ¬ P 
    -/
    assume np nnp,
    /-
        (Case 1)
        np : ¬ P 
        nnp : ¬ ¬ P
        ⊢ false
        
        (Case 2)
        ¬ ¬ ¬ P → ¬ P 
    -/
    apply nnp,
    /-
        (Case 1)
        np : ¬ P 
        nnp : ¬ ¬ P
        ⊢ ¬ P 
        
        (Case 2)
        ¬ ¬ ¬ P → ¬ P 
    -/
    exact np,
    /-
        Gets rid of Case 1
    -/
    assume nnnp p,
    /-
        (Case 2)
        nnnp : ¬ ¬ ¬ P
        p : P
        ⊢ false
    -/
    apply nnnp,
    /-
        (Case 2)
        nnnp : ¬ ¬ ¬ P
        p : P
        ⊢ ¬ ¬ P 
    -/
    assume np,
    /-
        (Case 2)
        nnnp : ¬ ¬ ¬ P
        p : P
        np : ¬ P  
        ⊢ false 
    -/
    apply np,
    /-
        (Case 2)
        nnnp : ¬ ¬ ¬ P
        p : P
        np : ¬ P  
        ⊢ P 
    -/
    exact p
    /-
        No goals (Gets rid of Case 2)
    -/
end


theorem p10 : ((P → Q) → P) → P :=
begin
  assume pqp,
  apply raa,
  assume nnp,
  apply nnp,
  apply pqp,
  assume p,
  have f : false,
  apply nnp,
  exact p,
  cases f,
end
