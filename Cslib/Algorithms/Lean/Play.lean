
module

public import Cslib.Init
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.List.Basic

@[expose] public section

namespace Cslib.Algorithms.Lean

def add3 (x : ℕ) : ℕ := x + 3

def time2 (x : ℕ) : ℕ := x * 2

#eval [time2, add3] <*> [1, 2, 3]

#eval (add3) <$> some 2

#eval some (add3) <*> some 2

#check (· + ·) <$> (some 2)

end Cslib.Algorithms.Lean
