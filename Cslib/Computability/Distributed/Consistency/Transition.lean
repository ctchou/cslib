/-
Copyright (c) 2026 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Cslib.Computability.Distributed.Consistency.Specification

/-! # Transitions

## References

* [*Principles of Eventual Consistency*][Burckhardt2014]
-/

@[expose] public section

namespace Cslib.DistributedConsistency

variable {State Operation Value Message Process : Type*}

inductive Transition (State Operation Value Message Process : Type*)
  | init : State → Set Message → Transition State Operation Value Message Process
  | call : Operation → State → State → Set Message →
    Transition State Operation Value Message Process
  | callret : Operation → State → State → Set Message → Value →
    Transition State Operation Value Message Process
  | recv : Message → State → State → Set Message →
    Transition State Operation Value Message Process
  | recvret : Message → State → State → Set Message → Value →
    Transition State Operation Value Message Process
  | step : Process → State → State → Set Message →
    Transition State Operation Value Message Process
  | stepret : Process → State → State → Set Message → Value →
    Transition State Operation Value Message Process

namespace Transition

def op : Transition State Operation Value Message Process → Option Operation
  | call o _ _ _ | callret o _ _ _ _ => some o
  | _ => none

def rcv : Transition State Operation Value Message Process → Option Message
  | recv m _ _ _ | recvret m _ _ _ _ => some m
  | _ => none

def proc : Transition State Operation Value Message Process → Option Process
  | step p _ _ _ | stepret p _ _ _ _ => some p
  | _ => none

def pre : Transition State Operation Value Message Process → Option State
  | call _ s _ _ | callret _ s _ _ _
  | recv _ s _ _ | recvret _ s _ _ _
  | step _ s _ _ | stepret _ s _ _ _ => some s
  | _ => none

def post : Transition State Operation Value Message Process → Option State
  | init s' _
  | call _ _ s' _ | callret _ _ s' _ _
  | recv _ _ s' _ | recvret _ _ s' _ _
  | step _ _ s' _ | stepret _ _ s' _ _ => some s'

def snd : Transition State Operation Value Message Process → Set Message
  | init _ ms
  | call _ _ _ ms | callret _ _ _ ms _
  | recv _ _ _ ms | recvret _ _ _ ms _
  | step _ _ _ ms | stepret _ _ _ ms _ => ms

def rval : Transition State Operation Value Message Process → Option Value
  | callret _ _ _ _ v
  | recvret _ _ _ _ v
  | stepret _ _ _ _ v => some v
  | _ => none

end Transition

end Cslib.DistributedConsistency
