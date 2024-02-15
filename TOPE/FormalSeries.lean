import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import Mathlib.Data.List.Func
import Mathlib.Algebra.Field.Basic

-- import Mathlib.Algebra.Order.Monoid.Cannonical.Defs

/-
    Note in general we want to prove the following
    theorem:

    exp(t(H₁ + H₀)) = ∑ₖ₌₀ to ∞ (∫dτ₀ … ∫dτₖ(
        ∑ₚ₌₁ to k δ(∑ p=1 to k (τₚ - t))
      )
    exp(τₖH₀)H₁ … exp(τ₀H₀)H₁
  )

-/

namespace Sequence

  abbrev Sequence (α : Type) := List α

  def BigOp (init : β) (seq : Sequence α) (op : β → β → β)
   (f : α → Bool × β ) : β :=
   match seq with
    | [] => init
    | a :: [] => if (f a).1 == true
                        then BigOp (op init (f a).2) ([]) op f
                        else BigOp init [] op f

    | a :: b :: seq' => if (f a).1 == true
                        then BigOp (op init (f a).2) (b::seq') op f
                        else BigOp init (b::seq') op f

  def InfSum (init : ℕ) (a : ℕ)
             (f : ℕ →  Matrix (Fin n) (Fin n) ℝ )
             : Matrix (Fin n) (Fin n) ℝ :=

    match a with
      | 0 => if a == init then f 0 else f 0
      | a + 1 => if a != init then f a + InfSum init a f else f init

end Sequence


namespace Test1

  -- We first need to open the appropriate namespaces
  open PowerSeries
  open Ring

  -- Define the formal power series in the ring of integers
  noncomputable def natPowerSeries : PowerSeries ℕ :=
    PowerSeries.mk (λ n ↦ n+1)

  noncomputable def myPower : PowerSeries ℕ :=
    2 • PowerSeries.X

  noncomputable def myPower2 : PowerSeries ℕ :=
    PowerSeries.mk (λ _ ↦ 2 )

  #print myPower

  /-
    PowerSeries.coeff_mul
  -/
  theorem equivPowSeries : PowerSeries.coeff ℕ 1 myPower = PowerSeries.coeff ℕ 3 myPower2 := by
    unfold myPower2
    rw [PowerSeries.coeff_mk]
    unfold myPower
    unfold X
    simp

    rw [PowerSeries.coeff_one_X]

    -- rw [PowerSeries.X_eq]
    -- simp

    -- apply PowerSeries.coeff_monomial_same


  theorem equiv2 : (PowerSeries.coeff ℕ 1) myPower = 2 := by
    simp [myPower]

  -- Lets try multivariate power series

  theorem eqiv2 : (PowerSeries.coeff ℕ) 1 myPower  = 2 := by
    simp [myPower]

  theorem test3 : 6 = 3 + 3 := by simp

  theorem testSeries : PowerSeries ℕ :=
    λ x ↦ (x 0 + 1)

  theorem testSeries₂ : PowerSeries ℕ :=
    λ x ↦ (x 0 + 1)

  theorem testEQ : testSeries = testSeries₂ := by
    unfold testSeries
    unfold testSeries₂
    simp

end Test1

/-

  Look into using this library:
  Mathlib.MeasureTheory.Integral.SetIntegral

  Bochner Integral on L₁ Space
  https://github.com/leanprover-community/mathlib4/blob/
  a6cf8f57f81f8f3bd96736335bc05d624e610f0e/
  Mathlib/MeasureTheory/Integral/Bochner.lean#L665-L667

  Interval Integral
  https://leanprover-community.github.io/
  mathlib4_docs/Mathlib/MeasureTheory/
  Integral/IntervalIntegral.html#intervalIntegral

  Beta function
  https://leanprover-community.github.io/
  mathlib4_docs/Mathlib/Analysis/SpecialFunctions/
  Gamma/Beta.html

  Need to generalize this to multivariate
-/

namespace IteratedIntegral

  open MeasureTheory
  open Complex

  variable {n z: ℕ} {H H₀ H₁ P₀: Matrix (Fin n) (Fin n) ℝ}

  instance normedAddCommGroup : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) :=
    sorry

  instance normedSpace : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
    sorry

  noncomputable def myThing (t : ℝ ):= t • (H₀ + H₁)

  noncomputable def checkIntegral {μ : Measure (ℝ)} (f : ℝ → Matrix (Fin n) (Fin n) ℝ ) :=
    integral μ f

  noncomputable def checkSetIntegral {μ : Measure (ℝ)} (s : Set ℝ ) (f : ℝ → Matrix (Fin n) (Fin n) ℝ ) :=
    integral (Measure.restrict μ s) f

  -- noncomputable def beta_function
  /-
    def iteratedIntegral (n : ℕ) (f : ℕ → Finset (Set ℝ) ): ℕ :=
      Nat.recOn n 0 (fun x => x+1)
  -/

  def empty : Matrix (Fin n) (Fin n) ℝ := 0

  /-
    We need to be able to index into different
    Sets (that are finite) to

    Add the accumulator
  -/
  noncomputable def testMotive {μ : Measure (ℝ ) } (n: ℕ ) (ix : ℕ → Set ℝ )
    (f : ℝ → Matrix (Fin n) (Fin n) ℝ ) (k : ℕ ) (init : Matrix (Fin n) (Fin n) ℝ)
    : Matrix (Fin n) (Fin n) ℝ :=
    match k with
    | 0 => init
    | k + 1 => (
        @checkSetIntegral n μ (ix k) (f)
      )

  /-
    TODO:
    Are you sure you have the motive correct?
    You need to accumulate at each step k.
  -/
  noncomputable def iteratedIntegral {μ : Measure ℝ  } {n : ℕ } (k : ℕ) (ix : ℕ → (Set ℝ) )
    (f : ℝ → Matrix (Fin n) (Fin n) ℝ )
    : Matrix (Fin n) (Fin n) ℝ :=
    Nat.recOn k empty (@testMotive μ n (ix) f)

  /-
    Need to compose each step in the integral.

    TODO: Check if this is correct...

    The bounds if integration are the same, between
    [0,1].

    I think f needs to take in multiple
    values of ℝ?
  -/
  noncomputable def iteratedIntegral' {μ : Measure ℝ } {n : ℕ} (k : ℕ ) (ix : ℕ → (Set ℝ ) )
  (f : ℝ → Matrix (Fin n) (Fin n) ℝ ) : Matrix (Fin n) (Fin n) ℝ  :=
    match k with
      | 0 => @checkSetIntegral n μ (ix 0) f
      | k + 1 => @checkSetIntegral n μ (ix k) (
        fun _ => @iteratedIntegral' μ n k ix f
  )

#check betaIntegral

/-
But also use this:
  https://leanprover-community.github.io/
  mathlib4_docs/Mathlib/Analysis/SpecialFunctions/
  Gamma/Basic.html#Complex.Gamma_nat_eq_factorial

  Use this theorem:
  Gamma_mul_Gamma_eq_betaIntegral

  Note we might have to convert the reals to complex to use the theorems
  using this function.
  https://leanprover-community.github.io/mathlib4_docs
  Mathlib/Data/Complex/Basic.html#Complex.ofReal'
-/

open DivisionSemiring

#check add_div
#check div_eq_mul_inv


theorem test_thm (a b c d: ℕ ) (h : c ≠ 0 ) : ( a + b = c * d) = ((a + b)/c = d) := calc
  (a + b = c * d) = ((a + b)/c =  d) := by rw [add_div]


#check Gamma_mul_Gamma_eq_betaIntegral
theorem alt_Gamma_mul_Gamma_eq_betaIntegral (s t : ℂ ) (hs : 0 < s.re) (ht : 0 < t.re) :
  (Gamma s * Gamma t = Gamma (s + t) * betaIntegral s t) = (
    (Gamma s * Gamma t)/ Gamma (s + t) = betaIntegral s t ) := by
    sorry


-- def iterateBetaIntegral (s : Finset ℕ ) (τ : s → ℂ ) (p : ∀ (k : s.attach ) , (τ k).re > 0 )


theorem isIn (k : ℕ) (s : Finset ℕ ): k + 1 ∈ s →  k ∈ s := by sorry

-- def realBetaIntegral (s t : ℝ) := betaintegral

#print betaIntegral
/-
  Assume that ∑ iₚ + 1 > 0 and iₚ > 0
-/
noncomputable def multivariateBetaIntegral (s : Finset ℕ ) (k : ℕ)
  (τ : ∀ (i : ℕ ), i ∈ s → ℂ ) (hp : k ∈ s )
  (p : ∀ (i : ℕ) (hi : i ∈ s), (τ i hi ).re > 0 ) : ℂ :=
  match k with
  | 0 => 1
  | k + 1 => betaIntegral (
      τ k (@isIn k s hp)) (multivariateBetaIntegral s k τ (@isIn k s hp) p
  )

noncomputable def multivariateBetaIntegral' (k : ℕ ) : ℝ :=
  match k with
  | 0 => 1
  | k + 1 => betaIntegral (
    )


#print Finset.sum
#check Finset.map
#print Multiset.sum
#check List.foldr


end IteratedIntegral

namespace RunLengthEncoding

  open Matrix
  open BigOperators

  variable {n z: ℕ} {H H₀ H₁ P₀: Matrix (Fin n) (Fin n) ℝ}
  variable {f : ℝ → ℝ }

  def test := (H₀)^3

end RunLengthEncoding

namespace MultinomialDirchletNormalization
  /-
    NOTE: You can think of MDN as the weight
    probability of interactions
  -/
end MultinomialDirchletNormalization

namespace TimeOrderedProduct

  open Matrix
  open BigOperators
  open Sequence
  open intervalIntegral

  variable (n : ℕ) (H H₀ H₁ : Matrix (Fin n) (Fin n) ℝ)
  variable (P₀ : ℝ )
  variable (f : ℝ → ℝ )
  variable {μ : Measure ℝ }

  noncomputable def S (t: ℝ ):= P₀ • exp ℝ (t • H)
  noncomputable def S₀ (z : ℕ ) (t: ℝ ):= P₀ • exp ℝ (t • H₀ + H₁ * z)

  instance nontriviallyNormedField : NontriviallyNormedField ℕ := sorry
  instance normedSpaceℕMat  : NormedSpace ℕ  (Matrix (Fin n) (Fin n) ℝ) := sorry

  /-
    exp((t⬝H)) = exp(t(H₀ +H₁))
  -/
  theorem addMatrixSplit (t: ℝ ) : (H = H₀ + H₁) →  P₀ •exp ℝ (t • H) = P₀ • (exp ℝ (t • (H₀ + H₁))) := by sorry


  /-
    Ordered Product
  -/
  noncomputable def Product₀ {l : List ℕ } (seq : Sequence { x: ℕ // x ∈ l  }  )
    (init : Matrix (Fin n) (Fin n) ℝ )
    (f : { x: ℕ // x ∈ l  } → Bool × Matrix (Fin n) (Fin n) ℝ ) :=
      BigOp init seq (λ x ↦ λ y ↦ x*y) (λ i ↦ f i)

  theorem oooof (l : ℕ) : List.foldr (λ _ ↦ λ x ↦ x*2) 1 (List.range (l)) = 2^l := by
    induction l with
    | zero => simp [List.range, List.foldr]
    | succ l ih => {
      rw [List.range_succ]
      simp
    }

  #print oooof
  #check List.range_succ

  /-
    Show that:
    f(x,y)ˡ = ∏ f(x,y) from 0 to l
  -/
  theorem ordered_prod_eq_exp {l : List ℕ } (seq : Sequence { x: ℕ // x ∈ l  }  )
    (init : Matrix (Fin n) (Fin n) ℝ )
    (f : { x: ℕ // x ∈ l  } → Bool × Matrix (Fin n) (Fin n) ℝ )  :

    BigOp init seq (λ x ↦ λ y ↦ x*y) (λ i ↦ f i) = (init)^(List.length l)  := by
    unfold BigOp
    simp [*]


  noncomputable def testFun (t : ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
    λ z ↦ PowerSeries.X z

  -- instance : HMul PowerSeries

  def Z := 1

  -- instance oof : HSMul (ℕ) (PowerSeries ℕ) := by sorry
  noncomputable def getCoeff (n : ℕ ) := PowerSeries.coeff (ℕ) n

  #check exp

  #check @Nat.cast ℝ Real.natCast (Nat.factorial 1)

  def toR (n : ℕ ) := @Nat.cast ℝ Real.natCast  n

  /-
    Initial Generating Function
  -/
  noncomputable def generatingFunction'₀ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
  P₀ • PowerSeries.mk (λ k ↦ (
      Z^k • (Nat.factorial (k ))⁻¹ • (
        iteratedDeriv (k  ) (λ _ ↦ exp ℝ (t • (H₀ + Z • H₁ )) ) 0
      )
    )
  )

  #check (H₀ + Z • H₁)^3

  noncomputable def generatingFunction'₁ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    P₀ • PowerSeries.mk (λ k ↦ (
      Z^k • (Nat.factorial (k) )⁻¹ • (iteratedDeriv (k) (
      λ _ ↦ ∑' (l : ℕ ), (
          (toR (Nat.factorial l ))⁻¹ • ((t • (H₀ + Z • H₁))^l)
        )
      ) 0)
      )
    )

  noncomputable def generatingFunction'₂ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    P₀ • PowerSeries.mk (λ k ↦ (
      Z^k • (Nat.factorial (k) )⁻¹ • (iteratedDeriv (k) (
      λ _ ↦ ∑' (l : ℕ ), (
          (toR (Nat.factorial l ))⁻¹ • ((t • (
            Finset.sum {0, 1} λ x ↦ H₀^(1-x) * (Z • H₁ )^(x)
            )
          )^l)
        )
      ) 0)
      )
    )

  noncomputable def generatingFunction''₂ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    P₀ • PowerSeries.mk (
    λ k ↦ (
      Z^k • (Nat.factorial k )⁻¹ • (iteratedDeriv (k) (
        λ _ ↦ ∑' (l : ℕ ), (
            (toR (Nat.factorial l ))⁻¹ • ((t • (
              Product₀ n (List.range (l)).attach (H₀+H₁) (
                λ m ↦ (
                        m.1 == m.1,
                        Finset.sum {0, 1} (λ j ↦ H₀^(1-j) * (Z • H₁)^(j)
                    )
                  )
                )
                )
              )
            )
          )
        ) 0)
      )
    )

  def t₁ (k : ℕ ): ℕ → Finset ℕ
    | i => if i <= k then {0, 1} else ∅

  def t₂ (k l : ℕ ): ℕ → Finset ℕ
    | i => if i <= k then Finset.range (l) else ∅

  -- TODO: Check, do we invoke some axiom of choice?
  noncomputable def t₃ (k l a : ℕ ): ℕ → ℕ
    | i => if i <= k then a else l


  def setOneTwo : Set ℕ := λ n ↦ (n = 1 ∨ n = 2)
  /-
    Defining t so I can use Set.pi for my infinite sequence.
  -/
  def t₄ (k : ℕ ) : ℕ → Set ℕ
    | i => if i <= k then setOneTwo else ∅

  def my_n : Set ℕ := λ (n : ℕ ) ↦ (true)
  /-
    FIXME: Need to distribute the t ahead of time
  -/
  noncomputable def generatingFunction₃ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
   P₀ • PowerSeries.mk (
    λ k ↦ (
      Z^k • (Nat.factorial (k) )⁻¹ • (iteratedDeriv (k) (
      λ _ ↦ ∑' (l : ℕ ), (
          (↑(Nat.factorial l ))⁻¹ • ((t • (
            Finset.sum (
              (Finset.pi (Finset.range l ) (t₁ l))
            )
              (
                λ j ↦ (
                  Product₀ n ( (List.range l).attach ) (H₀*H₁) (
                    λ m ↦(m == m, H₀^(1 - (j m.1 m.2))*(Z • H₁)^((j m.1 m.2))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      ) 0)
    )
  )

  /-
    TODO: Show that you apply iterated deriv to get rid of z
  -/

  /-
    TODO: How do we related the infite sum with index l? How do
    we work with infinite Series?

    Just write a predicate on top of l everytime you use it
    as a wrapper.
  -/

  /-
    What you want is any subset is equal to k
  -/
  def addsToK {s : Finset ℕ } (k : ℕ ) (f : (a : ℕ) → a ∈ s  → ℕ) : Prop
    := Finset.sum (s.attach) (λ i ↦ f (i.1) (i.2)) = k

  instance {s : Finset ℕ } {k : ℕ} (f : (a : ℕ) → a ∈ s  → ℕ) : Decidable (addsToK k f) := by sorry

  /-
  def testFilter {s : Finset ℕ } (x : ℕ ) (st : Finset ((a : ℕ) → a ∈ s  → ℕ)) : Finset ((a : ℕ) → a ∈ s  → ℕ) :=
    Finset.filter (addsToK x ) st
  -/

  #eval List.Func.get 1 [1,0,3]

  def filterSequenceUpTo {s : Finset ℕ } (k : ℕ ) (st : Finset ((a : ℕ) → a ∈ s  → ℕ))
    : Finset ((a : ℕ) → a ∈ s  → ℕ) :=
    Finset.filter (addsToK k) st

  /-
    Removing the Derivative and then
    setting a condition on the Finset.pi
    that we only have j_m such that

    ∑ j_m from 0 to l = k

    Note that k goes from z Unit.unit

    This is before RLE
  -/
  noncomputable def generatingFunction₄ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    P₀ • PowerSeries.mk (
      λ k ↦ (
        ∑' (l : ℕ ), (
            Z^k • (↑(Nat.factorial l ))⁻¹ • ((t • (
              Finset.sum (
              filterSequenceUpTo (k) (Finset.pi (Finset.range l ) (t₁ l))
              )
                (
                  λ j ↦ (
                    Product₀ n ( (List.range l).attach ) (H₀*H₁) (
                      λ m ↦(m == m, H₀^(1 - (j m.1 m.2))*(H₁)^((j m.1 m.2))
                        )
                      )
                    )
                  )
                )
              )
            )
          )
      )
    )

  /-
    Applying Runtime Length Encoding

    should have a function that takes in
    a j m and return an i that takes a p

    j_m ↦ i_p where 1 ≤ m ≤ l and 0 ≤ k ≤ p

  -/

  /-
    Just need to pattern match with totalLength to return a sequence
    of i_p.


    So what we have is that j is essentially a sequence indexed by s.
    We need to make a new sequence i that is going to be indexed
    by k.

    So we will need to prove that runLength encoding has a length that is less
    than k.
  -/

  /-
    RLE on a list
  -/
  def testw := (Finset.pi (Finset.range 5 ) (t₁ 5))
  def runLengthEncoding (acc : ℕ) (l : List ℕ ) : List ℕ  :=
    match l with
      | [] => (acc)::[]
      | x::xs => if x == 0 then runLengthEncoding (acc+1) xs else
        (acc) :: runLengthEncoding 0 xs

  def runLengthEncoding2 (acc : ℕ) (l : List ℕ ) : List ℕ  :=
    match l with
      | [] => (acc)::[]
      | x::xs => if x == 0 then runLengthEncoding (acc+1) xs else
        (acc) :: runLengthEncoding 0 xs

  /-
    Given an infinite sequence f, give the run length
    encoding up to k.
  -/
  def runLengthEncodingSeq (f : ℕ → ℕ) (acc : ℕ ) (k : ℕ)  : ℕ:=
    match k with
    | 0 => acc
    | k + 1 => if (f k) == 0 then runLengthEncodingSeq f (acc+1) k else
    runLengthEncodingSeq f 0 k

  /-
    RLE on a Finset
  -/
  def getInSet {s : Finset ℕ } (p : a+1 ∈ s) : a ∈ s := by sorry
  def zeroInSet {s : Finset ℕ } (p : 0 ∈ s) : a ∈ s := by sorry

  /-
    You need to have this take the proof that p ∈ Finset.range k
    Which then gets converted to a proof that p ∈ Finset.range l

    Which can be done by supplying the following theorem:
    f is essentially a sequence

  -/
  def rleFin {s : Finset ℕ}
    (acc : ℕ)  (f : (a : ℕ) → a ∈ s  → ℕ) (a : ℕ) (p : a ∈ s ) : ℕ :=
    match a with
      | 0 => acc
      | a + 1 => if f a (getInSet p) == 0 then
         rleFin (acc+1) f a (getInSet p)
        else rleFin 0 f a (getInSet p)

-- Here s gives us the length of our sequence. i.e. a finite sequence.
-- The cardinality of s₀ should be k and the cardinality of s should be l
def rleFin2 {s : Finset ℕ} {s₀ : Finset ℕ } {p: s₀ ⊆ s }
    (f : (a : ℕ) → a ∈ s  → ℕ) (a : ℕ) (p : a ∈ s ) : (a : ℕ) → a ∈ s₀ → ℕ :=
    match a with
      | 0 => fun h => fun b => Finset.card s₀
      | a + 1 =>
        fun h =>
          fun b =>
            match h with
              | _ => f a (getInSet p)

  /-
    Runlength encoding substitution

    Skipping down to equation 5:
  -/
  noncomputable def generatingFunction₅ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    P₀ • PowerSeries.mk (
      λ k ↦ (
        ∑' (l : ℕ ), (
            Z^k • (↑(Nat.factorial (l + k ) ))⁻¹ • ((t • (
              Finset.sum (
                filterSequenceUpTo (l) (
                    Finset.image (λ x ↦ rleFin 0 x ) (
                      Finset.pi (Finset.range l ) (t₁ l)
                  )
                )
              )
                (
                  λ i ↦ (
                    Product₀ n ( (List.range (l ) ).attach ) (H₀*H₁) (
                      λ m ↦(m.1 ≤ (k), H₀*(H₁)^(
                            i m.1 m.2
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
      )
    )

  /-
    Turn this 1/(l+k) ! to

    ∏ from p=0 to k (iₚ)!/(∑ from p=0 to k (iₚ + k)! )
    and then divide each (tH₀)ⁱᵏ by (iₖ)!

    Now why is this true?

  -/


  /-
    Equation 6:

    Note lets use the fact that:
      ∑ (from p=0 to k) iₚ = l

  -/

  theorem test₀ (k l : ℕ ): k ≤ l → x ∈ Finset.range l → x ∈ Finset.range k := by sorry

  lemma ixSum (k l: ℕ ) (p : k ≤ l ):  ∀ f ∈ (Finset.pi (Finset.range k) (t₁ l)),
    (Finset.sum (Finset.range l).attach (λ i ↦ f i.1 (test₀ k l p i.2 ) )) = l := by sorry

  -- scoped notation "{" p "| ≤ " l "}" => Finset.range (1)

  noncomputable def generatingFunction₆ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
  P₀ • PowerSeries.mk (
    λ k ↦ (
      ∑' (l : ℕ ), (
          (t • (
            Finset.sum (

              -- This part tells us that every f adds up to l
              filterSequenceUpTo (l) (
                  Finset.image (λ x ↦ rleFin 0 x ) (
                    Finset.pi (Finset.range k ) (t₂ k l)
                )
                -- After applying rleFin we should have a sequence of
                -- size k
             )
             -- Note that this is a sequence of size l though

            )
              (
                λ i ↦ (

                  Nat.factorial (
                    Finset.prod ((Finset.range k ).attach ) (
                      λ p ↦ i p.1 (p.2)
                    )
                  )
                  • Nat.factorial (
                      Finset.sum ((Finset.range k).attach ) (
                        λ p ↦ i p.1 (p.2)
                      ) + k
                    )^(-1)
                  •
                  Product₀ n ( (List.range k ).attach ) (H₀*H₁) (

                    λ m ↦(
                        m.1 ≤ k,
                        Nat.factorial (i m.1 m.2) •
                        H₀ * (H₁)^(i m.1 m.2)
                      )
                    )

                  )
                )
              )
          )
        )
    )
  )

  /-
    TODO:
    Need to somehow combine summations
  -/
  noncomputable def generatingFunction₇ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
  P₀ • PowerSeries.mk (
    λ k ↦ (
      ∑' (l : ℕ ), (
          (t • (
            Finset.sum (

              -- This part tells us that every f adds up to l
              filterSequenceUpTo (l) (
                  Finset.image (λ x ↦ rleFin 0 x ) (
                    Finset.pi (Finset.range k ) (t₂ k l)
                )
                -- After applying rleFin we should have a sequence of
                -- size k
             )
             -- Note that this is a sequence of size l though

            )
              (
                λ i ↦ (

                  Nat.factorial (
                    Finset.prod ((Finset.range k).attach ) (
                      λ p ↦ i p.1 (p.2)
                    )
                  )
                  • Nat.factorial (
                      Finset.sum ((Finset.range k).attach ) (
                        λ p ↦ i p.1 (p.2)
                      ) + k
                    )^(-1)
                  •
                  Product₀ n ( (List.range k ).attach ) (H₀*H₁) (

                    λ m ↦(m.1 ≤ k,
                        Nat.factorial (i m.1 m.2) •
                        H₀ * (H₁)^(i m.1 m.2)
                      )
                    )

                  )
                )
              )
          )
        )
    )
  )

  def set_over_t (t : ℝ ) (n : ℕ) : Set ℝ :=
    match n with
    | _ => {τ | 0 ≤ τ ∧ τ ≤ t }

  /-
    What exactly is τ doing?

    You can think of τ as the smooth version of
    iₚ. The gamma function interpolates between
    the sequences when iₚ appears
  -/
  noncomputable def myDirac (k : ℕ ) (τ : ℕ → ℝ  ) :=
    MeasureTheory.Measure.dirac (
      Finset.sum (Finset.range k) (
        λ p ↦ (τ p)
      )
    )

  noncomputable def dirac_delta (x₀ x₁ : ℝ ) := if x₀ ≠  x₁ then 1 else 0

  noncomputable def check (t : ℝ) := 1 - t

  /-
    We want to say somthing like
  noncomputable def generatingFunction₁₂ (t : ℝ): PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    PowerSeries.mk (
        λ k ↦ (
          Z^k • (@IteratedIntegral.iteratedIntegral' μ n (k) (set_over_t t))
         λ τ ↦ (
          dirac_delta 0 (
              Finset.sum (Finset.range (k)) (
                λ p ↦ (set_over_t t p) + t
              )
            )
          ) •
          (H₀  + H₁)
         )
      )
  -/

open IteratedIntegral


/-
  Should take in a run length encoding and return a set of
  τ.

  How does it know how to return τ? well

  Well τ is actually just the rle
-/

  def mySet : Set ℕ := λ n ↦ true

  instance : Nonempty (mySet) := by sorry

  theorem isNotEmpty : mySet → Nonempty (Set ℕ ) := by
    sorry

  #check Classical.choice mySet

/-
  This is my RLE now I just need to pass this to multivariateBetaIntegral

  Q: How do I iterate over the Finite set of my RLE?
  A: Turned this into a list

  Q: How do I turn my ℕ → ℂ?
  A: use the toℂ below
-/
def toℂ (n : ℕ ) := Complex.ofReal' (@Nat.cast ℝ Real.natCast n)

def convert {l : ℕ } (f : i ∈ Finset.range l → ℕ) (p : i ∈ Finset.range l)
: i ∈ Finset.range l → ℂ :=
  fun h => toℂ (f p)

/-
  RLE set
-/
noncomputable def τₚ (l : ℕ ) :=
  Finset.image (
      λ x ↦ (rleFin 0 x)
  ) (Finset.pi (Finset.range l ) (t₁ l))

noncomputable def τApply (l : ℕ ) := List.foldr (
  λ x ↦ (λ y ↦ (y + x.1) )
) 0 ((List.range l).attach)


def myTuple : List (ℕ × ℕ)  := List.zip [1,2,3] [1,2,3]

/-
TimeOrderedProduct.τₚ (l : ℕ) : List ((a : ℕ) → a ∈ Finset.range l → ℕ)
-/

/-
  We need something like Finset.sum but not over summation.
  We need to go over a range k and then foldr?

  The issue is that each element in τₚ requires proof that
  it is in the range l.

  Solution:
  Prod.mk ((List.range l).attach, RLE)

  Then do a foldr on this.
-/



/-
  TODO: just define MVB here passing in a k and just
  use τₚ here.

  Note that rleFin is a run length encoding on a finite set
  I need to do runlength encoding on potentially
  infinite
-/

/-
noncomputable def betaIntegralIterated (k : ℕ) :=
  List.foldr (λ x ↦λ y ↦ ∫ (x : ℝ ) in (0) .. 1,
  ) (List.range k)
-/

-- intervalIntegral (λ i ↦ i • x) 0 1

-- noncomputable def matrIntegral (k : ℕ ) (x : Matrix (Fin n) (Fin n) ℝ ) :=
  -- intervalIntegral (λ i ↦ i • x) 0 1

  -- ∫ (x : ℝ ) in (0) .. 1, (λ x ↦ 1)

/-
  TODO:
  Need to apply i and j to τₚ

  What is the best way to apply τₚ
-/
noncomputable def applyMVB (k : ℕ) (p : ℕ →  ℕ ) := (
    List.foldr
    (λ i ↦ λ j ↦ Complex.betaIntegral (p i) j)
    1
    (List.range (k) )
)

-- List.foldr (λ i ↦ λ j ↦ i) 0 (List.range (k))
-- multivariateBetaIntegral (Finset.range (k)) k


#check intervalIntegral

noncomputable def iteratedIntervalIntegral (k : ℕ ) (init : ℝ ) (f : ℝ → ℝ ) :=
  match k with
  | 0 => Set.indicator (Set.singleton 1) (λ_ ↦ toR 1) (init)
  | k + 1 => intervalIntegral (
    λ τ ↦
    iteratedIntervalIntegral k (τ + init) f
  ) 0 1 μ

/-
  Final Form
-/
noncomputable def generatingFunction₁₂ (t : ℝ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
  P₀ • PowerSeries.mk (
    λ k ↦
     (
      List.foldr (
          λ _ ↦ λ j ↦ (
            intervalIntegral (
              λ τ ↦ List.foldr (
              -- Move the Set Inidcator In here
              λ _ ↦ (
                  λ α ↦ α * (exp ℝ ( τ • H₀)) * H₁
                )
            ) 1 (List.range (k) )
            ) 0 t μ
          )
          *
          Set.indicator (Set.singleton 1) (λ _ ↦ 1)
          (
           intervalIntegral (
            λ τ₀ ↦ List.foldr (
              λ _ ↦ λ τ₁  ↦ τ₀ + τ₁
            ) 0 (List.range k)
          ) 0 t μ
          - t
          )
        )
        1 (List.range k)
      )
    )

  theorem oof2 (x : ℕ) : x • H₀ = x * H₀ := by simp

  theorem oof : (exp ℝ H₀) = ∑' (n : ℕ ), ((Nat.factorial n))⁻¹ • (H₀ ^ n) := by

  unfold exp
  unfold FormalMultilinearSeries.sum
  unfold expSeries
  simp


  have p₀ (i : ℕ ):= (Nat.factorial i)⁻¹ • H₀ ^ i
  have p₁ (i : ℕ ):= (Nat.factorial i)⁻¹ * H₀ ^ i

  have p₂ : ∀ (i : ℕ ), (Nat.factorial i)⁻¹ • H₀ ^ i =
      (Nat.factorial i)⁻¹ * H₀ ^ i
      := by {
        intro q
        induction' q
        simp
        unfold Nat.factorial
        simp
      }

  have p₃ : ∑'(i : ℕ ) , (↑(Nat.factorial i)⁻¹) • H₀ ^ i
          = ∑'(n_1 : ℕ ) , (Nat.factorial n_1)⁻¹ • H₀ ^ n_1
          := by {simp }

  have p₄ := ∑'(i : ℕ ) , (Nat.factorial i)⁻¹ * H₀ ^ i

  rw [p₃]
  unfold Nat.cast
  simp
  rw [p₃]

    -- intro a b c


  /-
  simp
  -/


  theorem w : ∑'(x: ℕ), x = ∑'(l : ℕ), l := by
    rw [tsum_def]




  /-

  Using the following theorem:

  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Exponential.html#NormedSpace.expSeries_apply_eq
  -/
  theorem gf₀_is_eq_gf₁ : generatingFunction'₀ = generatingFunction'₁ := by

    unfold generatingFunction'₀
    unfold generatingFunction'₁
    unfold PowerSeries.mk
    unfold exp

    simp

    unfold expSeries
    unfold FormalMultilinearSeries.sum

    simp
    unfold Z
    simp
    unfold toR
    simp


  theorem gf₁_is_eq_gf₂ : generatingFunction'₁ = generatingFunction'₂ := by
    unfold generatingFunction'₁
    unfold generatingFunction'₂
    unfold Z
    simp

  #print gf₁_is_eq_gf₂

  theorem gf₂_is_eq_gf₂' : generatingFunction'₂ = generatingFunction''₂ := by
    unfold generatingFunction'₂
    unfold generatingFunction''₂
    unfold Z
    unfold Product₀
    simp


  theorem tope : generatingFunction'₀ = generatingFunction₁₂ := calc
    generatingFunction'₀ = generatingFunction'₁ := by apply gf₀_is_eq_gf₁
    _ = generatingFunction'₂ := by apply gf₁_is_eq_gf₂
    _ = generatingFunction''₂ := by sorry
    _ = generatingFunction₃ := by sorry
    _ = generatingFunction₄ := by sorry
    _ = generatingFunction₅ := by sorry
    _ = generatingFunction₆ := by sorry
    _ = generatingFunction₇ := by sorry
    _ = generatingFunction₁₂ := by sorry

end TimeOrderedProduct


namespace main
end main
