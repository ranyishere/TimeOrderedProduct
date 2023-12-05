

/-
  Define BigOperator Notation for Sequences
-/

def test (x : Int ) := 2*x + 3
def test2 (x : Int ) := x + 3

#check Nat.mul_sub_left_distrib
#check Int

theorem test_thm (x₀ x₁: Int) : -(x₀ + x₁) = -x₀ - x₁ := by
simp


/-
def test3 (x : Nat ) : test x - test2 x = x := by
  unfold test
  unfold test2
  -/
