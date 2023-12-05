import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv


namespace Test1

  -- We first need to open the appropriate namespaces
  open PowerSeries
  open Ring

  -- Define the formal power series in the ring of integers
  noncomputable def natPowerSeries : PowerSeries ℕ :=
    PowerSeries.mk (λ n ↦ n+1)

  noncomputable def myPower : PowerSeries ℕ :=
    2 • PowerSeries.X

  theorem equiv2 : (PowerSeries.coeff ℕ 1) myPower = 2 := by
    simp [myPower]

  -- Lets try multivariate power series

  theorem eqiv2 : (PowerSeries.coeff ℕ) 1 myPower  = 2 := by
    simp [myPower]

  #print equiv2

  theorem test3 : 6 = 3 + 3 := by simp

  theorem check [Ring ℕ ] (x : ℕ) : test1 x + test2 x = 6 + 2 * x := by

    unfold test1
    unfold test2
    rw [← add_assoc]
    rw [two_mul]
    rw [←  add_assoc]
    have h₀ (x : ℕ ) : 3 + x + 3 + x = 3 + 3 + x + x := by linarith
    rw [h₀]

  theorem testSeries : PowerSeries ℕ :=
    λ x ↦ (x 0 + 1)

  theorem testSeries₂ : PowerSeries ℕ :=
    λ x ↦ (x 0 + 1)

  theorem testEQ : testSeries = testSeries₂ := by
    unfold testSeries
    unfold testSeries₂
    simp

end Test1


namespace TestDerivative

  def myFun (x:ℝ ) := 3 + 2*x

  /-
    Probably use something like this:

    https://leanprover-community.github.io/
    mathlib4_docs/Mathlib/Analysis/
    Calculus/Deriv/Basic.html#deriv_eq
  -/
  theorem testDeriv (x: ℕ) : (deriv myFun x) = 1 := sorry

end TestDerivative


namespace RunLengthEncoding

  open Matrix
  open BigOperators

  variable {n z: ℕ} {H H₀ H₁: Matrix (Fin n) (Fin n) ℝ}
  variable {f : ℝ → ℝ }

  def test := (H₀)^3

  -- def t₀ (l : ℕ):= (H₀ + z • H₁)^l = ∏ x in (Finset.range l), H₀ + z • H₁


end RunLengthEncoding

namespace TimeOrderedProduct

  open Matrix
  open BigOperators

  variable (n : ℕ) (H H₀ H₁: Matrix (Fin n) (Fin n) ℝ)
  variable (f : ℝ → ℝ )

  noncomputable def S (t: ℝ ):= exp ℝ (t • H)
  noncomputable def S₀ (z : ℕ ) (t: ℝ ):= exp ℝ (t • H₀ + H₁ * z)

  instance normedAddCommGroup : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) :=
    sorry

  instance normedSpace : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    sorry

  instance nontriviallyNormedField : NontriviallyNormedField ℕ := sorry

  instance nontriviallyNormedFieldUnit : NontriviallyNormedField (Unit →₀ ℕ) := sorry

  instance normedSpaceUnit : NormedSpace (Unit →₀ ℕ )  (Matrix (Fin n) (Fin n) ℝ) :=
    sorry
  instance normedAddCommGroupR :  NormedAddCommGroup (ℝ → (Matrix (Fin n) (Fin n) ℝ)) :=
    sorry
  instance normedSpaceR : NormedSpace ℕ  (ℝ → Matrix (Fin n) (Fin n) ℝ) :=
    sorry

  instance normedSpaceR₀ : NormedSpace ℕ  (Matrix (Fin n) (Fin n) ℝ) :=
    sorry


  /-
    theorem generatingFunction2 (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
      λ z ↦ (exp ℝ (t • (H₀ + H₁ * (z 1))))
    noncomputable def test (t : ℝ) := λ (z: ℕ) ↦ exp ℝ (t • H₀ + H₁ * z)
  -/

  -- We need to do derivative of S at z = 0

  /-
    exp((t⬝H)) = exp(t(H₀ +H₁))
  -/
  theorem addMatrixSplit (t: ℝ ) : (H = H₀ + H₁) → ∃ (P₀ : ℝ) , exp ℝ (t • H) = P₀ • (exp ℝ (t • (H₀ + H₁))) := by sorry

  -- variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  -- variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

  /-
    Use Iterative Derivative
    https://leanprover-community.github.io/mathlib4_docs
    /Mathlib/Analysis/Calculus/
    IteratedDeriv.html#iteratedDerivWithin
  -/

  /-
    Q: Relate Unit →₀ ℕ to deriviative?

    Need to understand how coefficient extraction
    really works underneath the hood.

    The goal is to count how many times z is applied.
    ∑ₖ₌₀ to ∞ (∂^k wrt z exp(t(H₀ + H₁z)))z = 0 * p₀
  -/

  -- theorem testThm (x : ℝ  ): iteratedDeriv 1 (2 * x) 1 = 4 := sorry

  -- #check PowerSeries.coeff (PowerSeries ℕ ) 1
  -- def mySeries : PowerSeries ℕ := PowerSeries.mk (λ x ↦ 2*x)

  -- noncomputable def trunc : Polynomial ℕ := PowerSeries.trunc 5 mySeries
  -- #print Polynomial.coeff trunc 1

  -- Define a function to evaluate each term of the polynomial at a point x
  /-
    This should be k
  -/

  /-
  theorem generatingFunction₀ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
    λ z ↦ (z 1) • (exp ℝ (t • (H₀ + H₁ * (z 1))))
  theorem generatingFunction₁ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
    deriv (λ z ↦ (exp ℝ (t • (H₀ + H₁ * (z 1)))))
  -/

  -- #check FormalMultilinearSeries ℝ (Matrix (Fin n) (Fin n) ℝ)
  -- noncomputable def test_series : PowerSeries ℕ := (λ _ ↦ exp ℕ 3)
  -- theorem checkEq : PowerSeries.coeff test_series = exp ℕ 3 := sorry
  -- noncomputable def test₆ (n : ℕ ) (t : ℝ ):= ∑' n, ↑(Nat.factorial n)⁻¹ • (t • (H₀ + H₁ * (z ())))

  /-
    Initial Generating Function

    TODO: Add p₀ for initial condition.
  -/
  noncomputable def generatingFunction'₀ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
  λ z ↦ (iteratedDeriv (z Unit.unit ) (λ _ ↦ exp ℝ (t • (H₀ + H₁ * (z Unit.unit ))) ) 0)

  /-
    FIXME: There should be a factor that comes out when you do
    the derivative


  -/

  /-
    noncomputable def generatingFunction₀ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
    λ z ↦ exp ℝ (t • (H₀ + H₁ * (z Unit.unit )))
  -/

  -- theorem removeDeriv₀ : generatingFunction'₀ = generatingFunction₀ := by sorry

  noncomputable def generatingFunction'₁ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (iteratedDeriv (z Unit.unit ) (
      λ _ ↦ ∑' (k : ℕ ), (
        (↑(Nat.factorial k ))⁻¹ • ((t • (H₀ + H₁ * (z Unit.unit)))^k)
      )
    ) 0)

  /-
    FIXME: There should be a factor that comes out when you do
    the derivative
  -/
  noncomputable def generatingFunction₁ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ ∑' (k : ℕ ), (
      ((Nat.factorial k ))⁻¹ •( (t • (H₀ + H₁ * (z Unit.unit )))^k )
    )

  /-
    Now lets try to show that:
    exp ℝ (t • (H₀ + H₁ * (z Unit.unit )))
    = ∑ (k!)^-1 • Π xᵢ
    where xᵢ = (H₀ + H₁ * (z Unit.unit) ) and
    the product goes from 0 to k

    To prove generatingFunction₀ = generatingFunction₁
    use:
    https://leanprover-community.github.io/mathlib4_docs/
    Mathlib/Analysis/
    NormedSpace/Exponential.html#NormedSpace.exp_eq_tsum
  -/
  theorem eqvGen' : generatingFunction'₀ = generatingFunction'₁ := by
    unfold generatingFunction'₀
    unfold generatingFunction'₁

    funext
    rw [exp_eq_tsum]
    sorry

  theorem applyDeriv₁ : generatingFunction'₁ = generatingFunction'₁ := by sorry

  /-
  theorem eqvGen : generatingFunction₀ = generatingFunction₁ := by
    unfold generatingFunction₀
    unfold generatingFunction₁
    funext
    rw [exp_eq_tsum]
    simp [generatingFunction₀, generatingFunction₁]

    unfold tsum
    sorry
  -/

  /-
    This is one way to define my function of Hᵢ.
    Another way is perhaps just defining a polynomial
    https://leanprover-community.github.io/
    mathlib4_docs/Mathlib/Data/
    Polynomial/Basic.html#Polynomial.sum
  -/
  def Hᵢ (i : ℕ ) (z : ℕ ): Matrix (Fin n) (Fin n) ℝ :=
    match i with
      | 0 => H₀ * z
      | 1 => H₁ * z
      | _ => H₀ * z

  instance SMul : HSMul ℝ (ℕ → Matrix (Fin n) (Fin n) ℝ) := sorry

  theorem test₄ (a b: ℕ) : a + b = Finset.sum ({a, b}) (·+·):=  by
    rw [Finset.sum_eq_add]
    sorry

  /-
    TODO: Get HSMul to work with my function?

    I think I may have the definition of my
    ∑ wrong.
  -/
  noncomputable def generatingFunction₂ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ ∑' (k : ℕ ), (
      ((Nat.factorial k ))⁻¹ • ( (t •
          (
            ∑ i in {0, 1}, (Hᵢ i (z Unit.unit))
          )
        )^k
      )
    )

    --unfold exp
    --unfold FormalMultilinearSeries.sum

/-
  Note in general we want to prove the following
  theorem:

  exp(t(H₁ + H₀)) = ∑ₖ₌₀ to ∞ (∫dτ₀ … ∫dτₖ(
        ∑ₚ₌₁ to k (τₚ - t)
      )
    exp(τₖH₀)H₁ … exp(τ₀H₀)H₁
  )
-/

end TimeOrderedProduct
