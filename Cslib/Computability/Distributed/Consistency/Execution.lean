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

namespace Cslib.DistributedConsistency

variable {Event State Operation Value Message Process Role : Type*}

structure ConcreteExecution (Event State Operation Value Message Process Role : Type*) where
  [eo : Encodable Event]
  tr : Event → Transition State Operation Value Message Process
  role : Event → Role
  del : Event → Event → Prop

end Cslib.DistributedConsistency
