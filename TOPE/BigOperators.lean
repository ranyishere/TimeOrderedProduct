import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Ring.Pi
import Mathlib.Data.Real.Basic

/-
  Define BigOperator Notation for Sequences
-/


universe u

variable {α : Type u}

def BigOperator (n : ℕ) (init : Type α) := Id.run do

  let mut q := init

  for i in [0:n] do 
    q := i+1

  pure q