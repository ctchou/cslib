/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.Consistency.Encodable
public import Cslib.Computability.Distributed.Consistency.Transition

/-! # Concrete executions

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

open Encodable

namespace Cslib.DistributedConsistency

variable {Event State Operation Value Message Process Role : Type*}

structure Trajectory (Event State Operation Value Message Process : Type*) where
  [eo : Encodable Event]
  tr : Event → Transition State Operation Value Message Process

namespace Trajectory

variable (traj : Trajectory Event State Operation Value Message Process)

abbrev lt := traj.eo.lt
abbrev le := traj.eo.le
noncomputable abbrev pred := traj.eo.pred

abbrev op (x : Event) := (traj.tr x).op
abbrev rcv (x : Event) := (traj.tr x).rcv
abbrev proc (x : Event) := (traj.tr x).proc
abbrev pre (x : Event) := (traj.tr x).pre
abbrev post (x : Event) := (traj.tr x).post
abbrev snd (x : Event) := (traj.tr x).snd
abbrev rval (x : Event) := (traj.tr x).rval

abbrev IsCall (x : Event) := (traj.tr x).op.isSome
abbrev IsReturn (x : Event) := (traj.tr x).rval.isSome

structure WellFormed : Prop where
  state_sequence (x : Event) :
    (traj.pred x = x ∧ traj.pre x = none) ∨
    (traj.lt (traj.pred x) x ∧ traj.pre x = traj.post (traj.pred x))
  call_return_call (x y : Event) :
    traj.lt x y → traj.IsCall x → traj.IsCall y →
    ∃ z, traj.IsReturn z ∧ traj.le x z ∧ traj.lt z y
  returns_le_calls (x : Event) :
    {y | traj.le y x ∧ traj.IsReturn y}.ncard ≤ {y | traj.le y x ∧ traj.IsCall y}.ncard

def returnsAfter (x : Event) : Set Event := {y | traj.le x y ∧ traj.IsReturn y}

open Classical in
noncomputable def return? (x : Event) : Option Event :=
  if h : (traj.returnsAfter x).Nonempty then
    some (WellFounded.min (lt_wellFounded (en := traj.eo)) (traj.returnsAfter x) h)
  else none

end Trajectory

structure ConcreteExecution (Event State Operation Value Message Process Role : Type*) where
  [eo : Encodable Event]
  tr : Event → Transition State Operation Value Message Process
  role : Event → Role
  del : Event → Event → Prop

namespace ConcreteExecution

variable (exec : ConcreteExecution Event State Operation Value Message Process Role)

abbrev lt := exec.eo.lt
abbrev le := exec.eo.le
noncomputable abbrev pred := exec.eo.pred

abbrev op (x : Event) := (exec.tr x).op
abbrev rcv (x : Event) := (exec.tr x).rcv
abbrev proc (x : Event) := (exec.tr x).proc
abbrev pre (x : Event) := (exec.tr x).pre
abbrev post (x : Event) := (exec.tr x).post
abbrev snd (x : Event) := (exec.tr x).snd
abbrev rval (x : Event) := (exec.tr x).rval

open Classical in
noncomputable def trajectory (r : Role) :
    Trajectory {x : Event // exec.role x = r} State Operation Value Message Process where
  eo := Subtype.encodable (encA := exec.eo)
  tr := Subtype.restrict (fun x ↦ exec.role x = r) exec.tr

structure WellFormed : Prop where
  trajectory_wellFormed (r : Role) : (exec.trajectory r).WellFormed
  del_snd_lt_rcv (x y : Event) : exec.del x y → exec.lt x y ∧
    ∃ m, exec.rcv y = some m ∧ m ∈ exec.snd x
  del_sender_unique (x1 x2 y : Event) : exec.del x1 y → exec.del x2 y → x1 = x2

noncomputable def return? (x : Event) : Option Event :=
  (exec.trajectory (exec.role x)).return? ⟨x, rfl⟩

end ConcreteExecution

end Cslib.DistributedConsistency
