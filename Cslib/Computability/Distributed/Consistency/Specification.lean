/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.Consistency.Relation
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.Basic

/-! # Consistency specifications

## References
-/

@[expose] public section

namespace Cslib.DistributedConsistency

open Set Relation

variable {Event Operation Value Session : Type*}

structure BaseHistory (Event Operation Value Session : Type*) where
  op : Event → Operation
  se : Event → Session
  rb : Event → Event → Prop
  rval : Event → Option Value

def BaseHistory.so (h : BaseHistory Event Operation Value Session) (s : Session) :=
  restrict h.rb {x | h.se x = s}

structure History (Event Operation Value Session : Type*)
    extends bh : BaseHistory Event Operation Value Session where
  rb_strict_order : IsStrictOrder Event rb
  rb_pred_finite : ∀ x, (predecessors rb x).Finite
  rb_interval_order : IsIntervalOrder rb
  rb_rval_ne_none : ∀ x y, rb x y → rval x ≠ none
  so_strict_total_order : ∀ s, IsStrictTotalOrderOn {x | se x = s} (bh.so s)

structure AbstractExecution (Event Operation Value Session : Type*)
    extends History Event Operation Value Session where
  vis : Event → Event → Prop
  ar : Event → Event → Prop
  vis_acyclic : Acyclic vis
  vis_pred_finite : ∀ x, (predecessors vis x).Finite
  ar_strict_total_order : IsStrictTotalOrder Event ar

def AbstractExecution.hb (a : AbstractExecution Event Operation Value Session)
    (s : Session) : Event → Event → Prop :=
  TransGen fun x y ↦ a.so s x y ∨ a.vis x y

def AbstractExecution.nvs (a : AbstractExecution Event Operation Value Session)
    (x : Event) (s : Session) : Set Event :=
  { y | a.se y = s ∧ a.rb x y ∧ ¬ a.vis x y }

def History.Satisfies (h : History Event Operation Value Session)
    (p : AbstractExecution Event Operation Value Session → Prop) : Prop :=
  ∃ a : AbstractExecution Event Operation Value Session, a.toHistory = h ∧ p a

structure Context (Event Operation : Type*) where
  events : Set Event
  op : Event → Operation
  vis : Event → Event → Prop
  ar : Event → Event → Prop

abbrev ReplicatedData (Event Operation Value : Type*) :=
  Operation → Context Event Operation → Value

def ReadOnlyOp (d : ReplicatedData Event Operation Value) (o : Operation) : Prop :=
  ∀ o' : Operation, ∀ c : Context Event Operation, ∀ x ∈ c.events,
    c.op x = o → d o' c = d o' {c with events := c.events \ {x}}

namespace AbstractExecution

def ReadMyWrites (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s, a.so s ≤ a.vis

def MonotonicReads (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s x y z, a.vis x y → a.so s y z → a.vis x z

def ConsistentPrefix (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ x y z, a.ar x y → a.vis y z → a.se y ≠ a.se z → a.vis x z

def NoCircularCausality (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s, Acyclic (a.hb s)

def CausalArbitration (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s, a.hb s ≤ a.ar

def CausalVisibility (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ s, a.hb s ≤ a.vis

def Causality (a : AbstractExecution Event Operation Value Session) : Prop :=
  a.CausalArbitration ∧ a.CausalVisibility

def SingleOrder (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∃ xs : Set Event, (∀ x, x ∈ xs → a.rval x = none) ∧
    ∀ x y, a.vis x y ↔ a.ar x y ∧ ¬ x ∈ xs

def RealTime (a : AbstractExecution Event Operation Value Session) : Prop :=
  a.rb ≤ a.ar

def EventualVisibility (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ x : Event, ∀ s : Session, (a.nvs x s).Finite

def context (a : AbstractExecution Event Operation Value Session) (x : Event) :
    Context Event Operation where
  events := predecessors a.vis x
  op := a.op
  vis := a.vis
  ar := a.ar

def RVal (d : ReplicatedData Event Operation Value)
    (a : AbstractExecution Event Operation Value Session) : Prop :=
  ∀ x, a.rval x = d (a.op x) (a.context x)

def Linearizability (d : ReplicatedData Event Operation Value)
    (a : AbstractExecution Event Operation Value Session) : Prop :=
  a.SingleOrder ∧ a.RealTime ∧ a.RVal d

def SequentialConsistency (d : ReplicatedData Event Operation Value)
    (a : AbstractExecution Event Operation Value Session) : Prop :=
  a.SingleOrder ∧ a.ReadMyWrites ∧ a.RVal d

def CausalConsistency (d : ReplicatedData Event Operation Value)
    (a : AbstractExecution Event Operation Value Session) : Prop :=
  a.EventualVisibility ∧ a.Causality ∧ a.RVal d

def BasicEventualConsistency (d : ReplicatedData Event Operation Value)
    (a : AbstractExecution Event Operation Value Session) : Prop :=
  a.EventualVisibility ∧ a.NoCircularCausality ∧ a.RVal d

def QuiescentConsistency (d : ReplicatedData Event Operation Value)
    (a : AbstractExecution Event Operation Value Session) : Prop :=
  { x | ¬ ReadOnlyOp d (a.op x) }.Finite →
  ∃ c, ∀ s, { x | a.se = s ∧ d (a.op x) c ≠ a.rval x }.Finite

end AbstractExecution

end Cslib.DistributedConsistency
