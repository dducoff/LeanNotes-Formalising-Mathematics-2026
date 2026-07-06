/-
# Copyright and author credits
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Bhavik Mehta, Kevin Buzzard, Den Ducoff, Gemini 3.5

# Read Me First
A list of the tactics used in this file are available in LeanNotes wiki page: 
    https://leannotes.wiki/Courses+and+eBooks/Formalising+Mathematics+-+Metha/Sheet1.lean
-/

/-
## Worked examples
-/
import Mathlib.Tactic
variable (P Q R : Prop)

-- Every proposition implies itself.
example (hP : P) : P := by
  exact show P from hP

-- The implication truth table defines an implication to be true 
-- whenever the conclusion is assumed to be true, 
-- regardless of whether the premise is true or false.
example (hQ : Q) : P → Q := by
  -- intro shifts the goal to the concluion. The premise,`_hP`, is unneeded.
  intro (_hP : P) ; clear _hP 
  exact show Q from hQ

-- This is`Modus Ponens, MP: P -> Q, P ⊢ Q`
example (hPtoQ : P → Q) (hP : P) : Q := by
  apply hPtoQ at hP; rename' (hP : Q) => hQ -- `MP yields hQ : Q`
  exact show Q from hQ

-- ## Examples for you to try 

-- Every proposition implies itself.
example : P -> P := by
  intro (hP : P)
  exact show P from hP

-- Every proposition implies itself, no matter what its truth value is.
example : ¬P -> ¬P := by
  intro (h_notP : ¬P)
  exact show ¬P from h_notP


example : P → Q → P := by
  intro
    (hP : P)
    (_hQ : Q) 
  clear _hQ  -- `Q` is unneeded.
  assumption -- The goal is witnessed by `hP`.

-- `->` is transitive.
example : (P → Q) → (Q → R) → P → R := by
  intro 
    (hPtoQ : P → Q) 
    (hQtoR : Q -> R)
    (hP    : P)
  apply hPtoQ at hP; rename' (hP : Q) => hQ -- MP yields hQ : Q
  apply hQtoR at hQ; rename' (hQ : R) => hR -- MP yields hR : R
  exact show R from hR
