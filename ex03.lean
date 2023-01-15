/-
COMP2009-ACE

Exercise 03 (Bool)

    This exercise has 2 parts.

    The first part is "logic chess" which has slightly different rules
    than logic poker but see below. The 2nd part ass you to define
    operations on booleans correspoding to implication and universal 
    quantification and prove it correct.

    Don't worry, if you can't do the universal quantification part. 
    This is intended as a challenge and only counts for 20% of the 
    exercise. 
-/

namespace ex03

def bnot : bool → bool 
| tt := ff
| ff := tt 

def band : bool → bool → bool 
| tt b := b
| ff b := ff

def bor : bool → bool → bool 
| tt b := tt
| ff b := b

def is_tt : bool → Prop 
| tt := true
| ff := false
local notation x && y := band x y 
local notation x || y := bor x y

/-
If you get an error update your lean or use:
local notation x && y := band x y 
local notation x || y := bor x y
-/


prefix `!`:90 := bnot

/-
PART I (60%)
============
Logic chess

Unlike logic poker in logic chess there is no guessing. You either
prove the proposition or you prove its negation, for example if the
proposition is true, e.g. 

chx0) ∀ x : bool, x=x

then you just go ahead and prove it -/

theorem chx0 : ∀ x : bool, x=x :=
begin
  assume x,
  reflexivity
end

/- However, if the proposition is false, e.g.

chx1) ∀ x : bool, x ≠ x

then  you prove its negation -/

theorem chx1 : ¬ (∀ x : bool, x ≠ x) :=
begin
  assume h,
  have g : tt ≠ tt,
  apply h,
  apply g,
  reflexivity,
end

/-
For each of the following proposition either prove them or their negation.

ch01) ∀ x : bool, ! (! x) = x
ch02) ∀ x:bool,∃ y:bool, x ≠ y
ch03) ∃ x:bool,∀ y:bool, x ≠ y
ch04) ∀ x y : bool, x=y ∨ x ≠ y
ch05) ∃ x:bool, x=bnot x
ch06) ∀ x y z : bool, x=y ∨ x=z ∨ y=z
ch07) ∀ y:bool, ∃ x:bool, y = bnot x
ch08) ∀ x y : bool, ! x = ! y → x=y
ch09) ∃ b : bool, ∀ y:bool, b && y = y
ch10) ∃ b : bool, ∀ y:bool, b && y = b
-/
theorem ch01 : ∀ x : bool, ! (! x) = x :=
begin
    assume x,
    /-
        x : bool
        ⊢ ! (! x) = x
    -/
    cases x,
    /-
        (Case tt)
        ⊢ ! (! tt) = tt
    
        (Case ff)
        ⊢ ! (! ff) = ff
    -/
    refl,
    /-
        Gets rid of Case tt
    -/
    refl,
    /-
        No goals (Gets rid of Case ff)
    -/
end

theorem ch02 : ∀ x : bool, ∃ y : bool, x ≠ y :=
begin
    assume f,
    /-
        f : bool
        ⊢ ∃ y : bool, x ≠ y
    -/
    cases f,
    /-
        (Case ff)
        ⊢ ∃ y : bool, ff ≠ y

        (Case tt)
        ⊢ ∃ y : bool, tt ≠ y
    -/
    existsi tt,
     /-
        (Case ff)
        ⊢ ff ≠ tt

        (Case tt)
        ⊢ ∃ y : bool, ff ≠ y
    -/
    assume g,
    /-
        (Case ff)
        g : ff = tt
        ⊢ false

        (Case tt)
        ⊢ ∃ y : bool, tt ≠ y
    -/
    contradiction,
    /-
        Gets rid of Case ff
    -/
    existsi ff,
    /-
        (Case ff)
        ⊢ ∃ y : bool, tt ≠ ff
    -/
    assume h,
    /-
        (Case ff)
        h : tt = ff 
        ⊢ false
    -/
    contradiction,
    /-
        No goals (Gets rid of Case tt)
end

theorem ch03: ¬(∃ x:bool,∀ y:bool, x ≠ y) :=
begin
    assume x,
    /-
        x : ∃ x:bool,∀ y:bool, x ≠ y
        ⊢ false
    -/
    cases x with a b,
    /-
        a : bool
        b : ∀ y:bool, x ≠ y
        ⊢ false
    -/
    apply b,
    /-
        a : bool
        b : ∀ y:bool, x ≠ y
        ⊢ x = ?m_1
    -/
    refl,
    /-
        No goals
    -/
end

theorem ch04: ∀ x y : bool, x=y ∨ x ≠ y :=
begin
    assume x y,
    /-
        x : bool
        y : bool
        ⊢ x=y ∨ x ≠ y
    -/
    cases x,
    /-
        (Case ff)
        y : bool
        ⊢ ff =y ∨ ff ≠ y

        (Case tt)
         y : bool
        ⊢ tt =y ∨ tt ≠ y
    -/
    cases y,
    /-
        (Case ff, ff)
        ⊢ ff = ff ∨ ff ≠ ff

        (Case ff, tt)
        ⊢ ff = tt ∨ ff ≠ tt
        
        (Case tt)
         y : bool
        ⊢ tt =y ∨ tt ≠ y
    -/
    left,
    /-
        (Case ff, ff)
        ⊢ ff = ff 

        (Case ff, tt)
        ⊢ ff = tt ∨ ff ≠ tt
        
        (Case tt)
         y : bool
        ⊢ tt =y ∨ tt ≠ y
    -/
    refl,
    /-
        Gets rid of Case ff, ff
    -/
    right,
    /-
        (Case ff, tt)
        ⊢ ff ≠ tt
        
        (Case tt)
        y : bool
        ⊢ tt =y ∨ tt ≠ y
    -/  
    assume a,
    /-
        (Case ff, tt)
        a : ff = tt
        ⊢ false
        
        (Case tt)
        y : bool
        ⊢ tt =y ∨ tt ≠ y
    -/  
    contradiction,
    /-
        Gets rid of Case ff, tt
    -/
    cases y,
    /-
        (Case tt, ff)
        ⊢ tt = ff ∨ tt ≠ ff
        
        (Case tt, tt)
        ⊢ tt = tt ∨ tt ≠ tt
    -/  
    right,
    /-
        (Case tt, ff)
        ⊢ tt ≠ ff
        
        (Case tt, tt)
        ⊢ tt = tt ∨ tt ≠ tt
    -/  
    assume a,
    /-
        (Case tt, ff)
        a : tt = ff
        ⊢ false
        
        (Case tt, tt)
        ⊢ tt = tt ∨ tt ≠ tt
    -/  
    contradiction,
    /-
        Gets rid of Case tt, ff
    -/
    left,
    /-
        (Case tt, tt)
        ⊢ tt = tt 
    -/  
    refl,
    /-
        No goals (Gets rid of Case tt, tt)
    -/
end

theorem ch05: ¬ (∃ x:bool, x=bnot x) :=
begin
    assume x,
    /-
        ∃ x:bool, x=bnot x
        ⊢ false
    -/
    cases x with a b,
    /-
        a : bool
        b : a = !a
        ⊢ false
    -/
    cases a,
    /-
        (Case ff)
        b : ff = !ff
        ⊢ false
        
        (Case tt)
        b : tt = !tt
        ⊢ false
    -/
    contradiction,
    /-
        Gets rid of Case ff
    -/
    contradiction,
    /-
        No goals (Gets rid of Case tt)
    -/
end
theorem ch06: ∀ x y z : bool, x=y ∨ x=z ∨ y=z :=
begin
    assume x y z,
    /-
        x y z : bool
        ⊢ x=y ∨ x=z ∨ y=z
    -/
    cases x,
    /-
        (Case ff)
        y z : bool
        ⊢ ff = y ∨ ff = z ∨ y = z

        (Case tt)
        y z : bool
        ⊢ tt = y ∨ tt = z ∨ y = z
    -/
    cases y,
    /-
        (Case ff, ff)
        z : bool
        ⊢ ff = ff ∨ ff = z ∨ ff = z

        (Case ff, tt)
        z : bool
        ⊢ ff = tt ∨ ff = z ∨ tt = z

        (Case tt)
        y z : bool
        ⊢ tt = y ∨ tt = z ∨ y = z
    -/
    left,
    /-
        (Case ff, ff)
        z : bool
        ⊢ ff = ff

        (Case ff, tt)
        z : bool
        ⊢ ff = tt ∨ ff = z ∨ tt = z

        (Case tt)
        y z : bool
        ⊢ tt = y ∨ tt = z ∨ y = z
    -/
    refl,
    /-
        Gets rid of Case ff, ff
    -/
    cases z,
    /-
        (Case ff, tt, ff)
        ⊢ ff = tt ∨ ff = ff ∨ tt = ff

        (Case ff, tt, tt)
        ⊢ ff = tt ∨ ff = tt ∨ tt = tt

        (Case tt)
        y z : bool
        ⊢ tt = y ∨ tt = z ∨ y = z
    -/
    right,
    /-
        (Case ff, tt, ff)
        ⊢ ff = ff ∨ tt = ff

        (Case ff, tt, tt)
        ⊢ ff = tt ∨ ff = tt ∨ tt = tt

        (Case tt)
        y z : bool
        ⊢ tt = y ∨ tt = z ∨ y = z
    -/
    left,
    /-
        (Case ff, tt, ff)
        ⊢ ff = ff 

        (Case ff, tt, tt)
        ⊢ ff = tt ∨ ff = tt ∨ tt = tt

        (Case tt)
        y z : bool
        ⊢ tt = y ∨ tt = z ∨ y = z
    -/
    refl,
    /-
        Gets rid of Case ff, tt, ff
    -/
    right,
    /-
        (Case ff, tt, tt)
        ⊢ ff = tt ∨ tt = tt

        (Case tt)
        y z : bool
        ⊢ tt = y ∨ tt = z ∨ y = z
    -/
    right,
    /-
        (Case ff, tt, tt)
        ⊢ tt = tt

        (Case tt)
        y z : bool
        ⊢ tt = y ∨ tt = z ∨ y = z
    -/
    refl,
    /-
        Gets rid of Case ff, tt, tt
    -/
    cases y,
    /-
        (Case tt, ff)
        z : bool
        ⊢ tt = ff ∨ tt = z ∨ ff = z

        (Case tt, tt)
        z : bool
        ⊢ tt = tt ∨ tt = z ∨ tt = z

    -/
    cases z,
    /-
        (Case tt, ff, ff)
        ⊢ tt = ff ∨ tt = ff ∨ ff = ff

        (Case tt, ff, tt)
        ⊢ tt = ff ∨ tt = tt ∨ ff = tt

        (Case tt, tt)
        z : bool
        ⊢ tt = tt ∨ tt = z ∨ tt = z

    -/
    right,
    /-
        (Case tt, ff, ff)
        ⊢ tt = ff ∨ ff = ff

        (Case tt, ff, tt)
        ⊢ tt = ff ∨ tt = tt ∨ ff = tt

        (Case tt, tt)
        z : bool
        ⊢ tt = tt ∨ tt = z ∨ tt = z

    -/
    right,
    /-
        (Case tt, ff, ff)
        ⊢ ff = ff

        (Case tt, ff, tt)
        ⊢ tt = ff ∨ tt = tt ∨ ff = tt

        (Case tt, tt)
        z : bool
        ⊢ tt = tt ∨ tt = z ∨ tt = z

    -/
    refl,
    /-
        Gets rid of Case tt, ff, ff
    -/
    right,
    /-
        (Case tt, ff, tt)
        ⊢ tt = tt ∨ ff = tt

        (Case tt, tt)
        z : bool
        ⊢ tt = tt ∨ tt = z ∨ tt = z

    -/
    left,
    /-
        (Case tt, ff, tt)
        ⊢ tt = tt

        (Case tt, tt)
        z : bool
        ⊢ tt = tt ∨ tt = z ∨ tt = z
    -/
    refl,
    /-
        Gets rid of Case tt, ff, tt
    -/
    left,
    /-
        (Case tt, tt)
        z : bool
        ⊢ tt = tt
    -/
    refl,
    /-
        No goals (Case tt, tt)
    -/
end

theorem ch07 : ∀ y:bool, ∃ x:bool, y = ! x :=
begin
    assume y,
    /-
        y : bool
        ⊢ ∃ x:bool, y = ! x
    -/
    cases y,
    /-
        (Case ff)
        ⊢ ∃ x:bool, ff = ! x
    
        (Case tt)
        ⊢ ∃ x:bool, tt = ! x
    -/
    existsi tt,
    /-
        (Case ff)
        ff = !tt
    
        (Case tt)
        ⊢ ∃ x:bool, tt = ! x
    -/
    refl,
    /-
        Gets rid of Case ff
    -/
    existsi ff,
    /-
        (Case tt)
        ⊢ tt = !ff
    -/
    refl,
    /-
        No goals (gets rid of Case tt)
    -/
end

theorem ch09 : ∃ b : bool, ∀ y:bool, b && y = y :=
begin
    existsi tt,
    /-
        ∀ y:bool, tt && y = y
    -/
    assume a,
    /-
        a : bool,
        ⊢ tt && a = a
    -/
    refl,
    /-
        No goals
    -/
end

theorem ch10: ∃ b : bool, ∀ y:bool, b && y = b :=
begin
    existsi ff,
    /-
        ∀ y:bool, ff && y = ff
    -/
    assume y,
    /-
        y = bool
        ⊢ ff && y = ff
    -/
    refl,
    /-
        No goals
    -/
end
⊢
/- 
PART II (40%)
=============

Define operations 

implb :   bool → bool → bool 
allb  :   (bool → bool) → bool

show that it corresponds to implication on Prop, i.e. prove

theorem implb_ok : ∀ x y : bool , is_tt (implb x y) ↔ is_tt x → is_tt y 
theorem allb_ok : ∀ f : bool → bool, is_tt (allb f) ↔ ∀ x : bool, is_tt (f x) 

Remark: you can define implb by pattern matching or using previous 
boolean operations. In the latter case you need to write

def implb (x y : bool) := ...

allb can only be defined this way (since there is no pattern matching on 
functions), i.e.

def allb (f : bool → bool) := ...

(*) the allb part is difficult, you only loose 20% if you don't do it.
-/

end ex03

