/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Automata.NA.SafraConstruction.SafraTree
public meta import Cslib.Computability.Automata.NA.SafraConstruction.SafraTree
public import Mathlib.Data.Finset.Sort

/-! # Safra tree

-/

@[expose] public section

namespace Cslib

open Finset Std

section Format

variable {α S : Type*} [DecidableEq S]

def VTree.toFormat [Repr α] : VTree α → Format
  | {val, kids} =>
      let kids_fmt := Format.sbracket <|
        Format.joinSep (kids.map (fun k : VTree α ↦ k.toFormat)) ", "
      Format.bracket "{" f!"{repr val}, {kids_fmt}" "}"

instance [Repr α] : Repr (VTree α) where
  reprPrec t _ := t.toFormat

unsafe def SafraVal.toFormat [Repr S] : SafraVal S → Format
  | {set, stable, acc} =>
      Format.bracket "{" f!"{repr set}, {stable}, {acc}" "}"

unsafe instance [Repr S] : Repr (SafraVal S) where
  reprPrec t _ := t.toFormat

unsafe instance [Repr S] : Repr (SafraTree S) where
  reprPrec t _ := t.toFormat

end Format

namespace Test1

abbrev S := Fin 3

def accept : Finset S := {1}

def trans_a (set : Finset S) : Finset S :=
  (if 0 ∈ set then {0,1} else ∅) ∪
  (if 1 ∈ set then {2} else ∅) ∪
  (if 2 ∈ set then {1,2} else ∅)

def trans_c (set : Finset S) : Finset S :=
  if 1 ∈ set then {1} else ∅

def tree1 : SafraTree S := SafraTree.mk true false {0} []
def tree2 : SafraTree S := SafraTree.mk true false {0, 1} []
def tree3 : SafraTree S := SafraTree.mk true false {0, 1, 2} [SafraTree.mk true true {1, 2} []]

#eval tree1
#eval tree2

#eval tree1.next trans_a accept
#eval tree3.next trans_a accept

#eval tree1.next trans_c accept
#eval tree2.next trans_c accept

end Test1

namespace Test2

inductive S
  | a | b | c | d | e | f | g
  deriving DecidableEq, Repr

open S

def accept : Finset S := {c,f,g}

def trans (set : Finset S) : Finset S :=
  (if a ∈ set then {a,e,f,g} else ∅) ∪
  (if b ∈ set then {c,d} else ∅) ∪
  (if c ∈ set then {d} else ∅) ∪
  (if d ∈ set then {g} else ∅) ∪
  (if e ∈ set then {b} else ∅) ∪
  (if f ∈ set then {b,c} else ∅) ∪
  (if g ∈ set then {e,f} else ∅)

def tree : SafraTree S :=
  SafraTree.mk true false {a,b,c,d,e,f,g} [
    SafraTree.mk true false {b,e,f} [
      SafraTree.mk true false {e} [],
      SafraTree.mk true false {f} [],
    ],
    SafraTree.mk true false {c} [],
    SafraTree.mk true false {d,g} [
      SafraTree.mk true false {g} [],
    ],
  ]

#eval tree.next trans accept

end Test2

end Cslib
