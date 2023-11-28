import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic


namespace Test1

  -- We first need to open the appropriate namespaces
  open PowerSeries
  open Ring

  -- Define the formal power series in the ring of integers
  noncomputable def natPowerSeries : PowerSeries ℕ :=
    PowerSeries.mk (λ n ↦ n+1)

  noncomputable def myPower : PowerSeries ℕ :=
    PowerSeries.X

  theorem equiv2 : (PowerSeries.coeff ℕ 1) myPower = 1 := by
    simp [myPower]


  -- Lets try multivariate power series


  theorem eqiv2 : (PowerSeries.coeff ℕ) 1 myPower  = 1 := by
    simp [myPower]
  /-
    #print equiv2
    #check (PowerSeries.coeff ℕ) 1 myPower  = 1
    #check LinearMap.proj myPower  1
   -/


  def test1 (x : ℕ) := 3 + x
  def test2 (x : ℕ) := 3 + x


  theorem test3 : 6 = 3 + 3 := by simp

  #print test3


  theorem check [Ring ℕ ] (x : ℕ) : test1 x + test2 x = 6 + 2 * x := by
    unfold test1
    unfold test2
    rw [← add_assoc]
    rw [two_mul]
    rw [←  add_assoc]
    have h₀ (x : ℕ ) : 3 + x + 3 + x = 3 + 3 + x + x := by sorry
    rw [h₀]

  theorem testSeries : PowerSeries ℕ :=
    λ x ↦ (x 0 + 1)

end Test1


namespace TestDerivative

  def myFun (x:ℝ ) := 3 + 2*x

  #check (deriv myFun)

  /-
    Probably use something like this:

    https://leanprover-community.github.io/
    mathlib4_docs/Mathlib/Analysis/
    Calculus/Deriv/Basic.html#deriv_eq
  -/
  theorem testDeriv (x: ℕ) : (deriv myFun x) = 1 := sorry

end TestDerivative


/-

Maybe use this Taylor Within?
https://leanprover-community.github.io/mathlib4_docs/
Mathlib/Analysis/Calculus/Taylor.html
-/
namespace TimeOrderedProduct
  open Matrix

  variable {n : ℕ} {H H₀ H₁: Matrix (Fin n) (Fin n) ℝ}
  variable {f : ℝ → ℝ }

  noncomputable def S (t: ℝ ):= exp ℝ (t • H)
  noncomputable def S₀ (z : ℕ ) (t: ℝ ):= exp ℝ (t • H₀ + H₁ * z)

  #check S • (8: ℝ)

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


  #check S
  #check deriv S 0
  #check deriv S₀ 0
  #check S
  #print PowerSeries


  theorem generatingFunction2 (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
    λ z ↦ (exp ℝ (t • (H₀ + H₁ * (z 1))))

  noncomputable def test (t : ℝ) := λ (z: ℕ) ↦ exp ℝ (t • H₀ + H₁ * z)

  -- We need to do derivative of S at z = 0

  /-
    exp((t⬝H)) = exp(t(H₀ +H₁))
  -/
  theorem addMatrixSplit (t: ℝ ) : (H = H₀ + H₁) → ∃ (P₀ : ℝ) , exp ℝ (t • H) = P₀ • (exp ℝ (t • (H₀ + H₁))) := sorry

  #print deriv

  -- variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  -- variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

  #check Nat.rec

  /-
    Use Iterative Derivative
    https://leanprover-community.github.io/mathlib4_docs
    /Mathlib/Analysis/Calculus/
    IteratedDeriv.html#iteratedDerivWithin
  -/

  def check (f : ℕ → ℕ ) (x : ℕ ): ℕ → ℕ
  | 0 => f x
  | n => (check f x) n-1
  termination_by check f x n => n -1
  decreasing_by
    simp_wf

  def nthDerivative {𝕜 : Type u} {F : Type v} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : 𝕂 → F) (x : 𝕂) : ℕ → F
    | 0 => f x
    | n => (nthDerivative (deriv f) x (n-1))
  decreasing_by sorry

  /-
    Q: Relate Unit →₀ ℕ to deriviative?

    Need to understand how coefficient extraction
    really works underneath the hood.

    The goal is to count how many times z is applied.
    ∑ₖ₌₀ to ∞ (∂^k wrt z exp(t(H₀ + H₁z)))z=0 * p₀
  -/

  theorem generatingFunction₀ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
    λ z ↦ nthDerivative (λ _ ↦ (exp ℝ (t • (H₀ + H₁ * (z 1))))) z 0

  theorem generatingFunction (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
    deriv (λ z ↦ (exp ℝ (t • (H₀ + H₁ * (z 1)))))


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
