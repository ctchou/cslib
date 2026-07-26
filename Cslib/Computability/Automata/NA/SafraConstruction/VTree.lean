/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Init
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic

/-! # Variable-branching tree

-/

@[expose] public section

namespace Cslib

open Finset

structure VTree (α : Type*) where
  val : α
  kids : List (VTree α)

namespace VTree

variable {α : Type*}

@[elab_as_elim, induction_eliminator]
def induction {α : Type u} {motive : VTree α → Sort v}
    (mk : ∀ val kids, (∀ k ∈ kids, motive k) → motive (mk val kids))
    (t : VTree α) : motive t :=
  match t with
  | { val, kids } => mk val kids fun k _ => @induction α motive mk k

def Forall (p : VTree α → Prop) (t : VTree α) : Prop :=
  p t ∧ t.kids.Forall p

def paths : VTree α → Finset (List ℕ)
  | { kids := kids, .. } =>
    let kidsPaths (k : Fin kids.length) := (paths kids[k.val]).image (k.val :: ·)
    Finset.biUnion (Finset.univ : Finset <| Fin kids.length) kidsPaths
termination_by x => x
decreasing_by simp; grind [→ List.sizeOf_lt_of_mem, List.getElem_mem]

def findAux (p : α → Bool) (path : List ℕ) : VTree α → List ℕ
  | { val, kids } =>
    let i := kids.findIdx (fun k ↦ p k.val)
    if _ : i < kids.length then findAux p (path ++ [i]) kids[i] else path
termination_by x => x
decreasing_by simp; grind [→ List.sizeOf_lt_of_mem, List.getElem_mem]

def find (p : α → Bool) (t : VTree α) : List ℕ :=
  findAux p [] t

end VTree

end Cslib
