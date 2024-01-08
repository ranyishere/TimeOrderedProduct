import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv

import Mathlib.Data.List.Func

-- import Mathlib.Algebra.Order.Monoid.Cannonical.Defs

/-
    Note in general we want to prove the following
    theorem:

    exp(t(H₁ + H₀)) = ∑ₖ₌₀ to ∞ (∫dτ₀ … ∫dτₖ(
        ∑ₚ₌₁ to k (τₚ - t)
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

namespace IteratedIntegral

end IteratedIntegral

namespace RunLengthEncoding

  open Matrix
  open BigOperators

  variable {n z: ℕ} {H H₀ H₁ P₀: Matrix (Fin n) (Fin n) ℝ}
  variable {f : ℝ → ℝ }

  def test := (H₀)^3

  -- def t₀ (l : ℕ):= (H₀ + z • H₁)^l = ∏ x in (Finset.range l), H₀ + z • H₁


end RunLengthEncoding

namespace TimeOrderedProduct

  open Matrix
  open BigOperators
  open Sequence

  variable (n : ℕ) (H H₀ H₁ : Matrix (Fin n) (Fin n) ℝ)
  variable (P₀ : ℝ )
  variable (f : ℝ → ℝ )

  noncomputable def S (t: ℝ ):= P₀ • exp ℝ (t • H)
  noncomputable def S₀ (z : ℕ ) (t: ℝ ):= P₀ • exp ℝ (t • H₀ + H₁ * z)

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
  theorem addMatrixSplit (t: ℝ ) : (H = H₀ + H₁) →  P₀ •exp ℝ (t • H) = P₀ • (exp ℝ (t • (H₀ + H₁))) := by sorry

  -- variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
  -- variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

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


  noncomputable def Product₀ {l : List ℕ } (seq : Sequence { x: ℕ // x ∈ l  }  )
    (init : Matrix (Fin n) (Fin n) ℝ )
    (f : { x: ℕ // x ∈ l  } → Bool × Matrix (Fin n) (Fin n) ℝ ) :=
      BigOp init seq (λ x ↦ λ y ↦ x*y) (λ i ↦ f i)


  /-
    Initial Generating Function
  -/
  noncomputable def generatingFunction'₀ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
  λ z ↦ (
      (Nat.factorial (z Unit.unit))⁻¹ • (
        iteratedDeriv (z Unit.unit ) (λ _ ↦ exp ℝ (t • (H₀ + H₁ * (z Unit.unit ))) ) 0
      )
  )

  /-
    noncomputable def generatingFunction₀ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ) :=
    λ z ↦ exp ℝ (t • (H₀ + H₁ * (z Unit.unit )))
  -/

  noncomputable def generatingFunction'₁ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      (Nat.factorial (z Unit.unit) )⁻¹ • (iteratedDeriv (z Unit.unit ) (
      λ _ ↦ ∑' (l : ℕ ), (
          (↑(Nat.factorial l ))⁻¹ • ((t • (H₀ + H₁ * (z Unit.unit)))^l)
        )
      ) 0)
    )

  noncomputable def generatingFunction'₂ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      (Nat.factorial (z Unit.unit) )⁻¹ • (iteratedDeriv (z Unit.unit ) (
      λ _ ↦ ∑' (l : ℕ ), (
          (↑(Nat.factorial l ))⁻¹ • ((t • (
            Finset.sum {0, 1} λ x ↦ H₀^(1-x) * (H₁ * (z Unit.unit))^(x)
            )
          )^l)
        )
      ) 0)
    )

  noncomputable def generatingFunction''₂ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      (Nat.factorial (z Unit.unit) )⁻¹ • (iteratedDeriv (z Unit.unit ) (
      λ _ ↦ ∑' (l : ℕ ), (
          (↑(Nat.factorial l ))⁻¹ • ((t • (
            Product₀ n (List.range (l)).attach (H₀+H₁) (
              λ m ↦ (
                      m.1 == m.1,
                      Finset.sum {0, 1} (λ j ↦ H₀^(1-j) * (H₁ * (z Unit.unit))^(j)
                    )
              )
            ))
            )
          )
        )
      ) 0)
    )

  def t₁ (k : ℕ ): ℕ → Finset ℕ
    | i => if i <= k then {0, 1} else ∅

  def t₂ (k l : ℕ ): ℕ → Finset ℕ
    | i => if i <= k then Finset.range (l) else ∅

  -- Do we invoke some axiom of choice??
  def t₃ (k l a : ℕ ): ℕ → ℕ
    | i => if i <= k then a

  /-
    FIXME: Need to distribute the t ahead of time
  -/
  noncomputable def generatingFunction₃ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      (Nat.factorial (z Unit.unit) )⁻¹ • (iteratedDeriv (z Unit.unit ) (
      λ _ ↦ ∑' (l : ℕ ), (
          (↑(Nat.factorial l ))⁻¹ • ((t • (
            Finset.sum (
              (Finset.pi (Finset.range l ) (t₁ l))
            )
              (
                λ j ↦ (
                  Product₀ n ( (List.range l).attach ) (H₀*H₁) (
                    λ m ↦(m == m, H₀^(1 - (j m.1 m.2))*((z Unit.unit ) • H₁)^((j m.1 m.2))
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

  def filterSequenceUpTo {s : Finset ℕ } (k : ℕ ) (st : Finset ((a : ℕ) → a ∈ s  → ℕ)) : Finset ((a : ℕ) → a ∈ s  → ℕ) :=
    Finset.filter (addsToK k) st

  /-
    Removing the Derivative and then
    setting a condition on the Finset.pi
    that we only have j_m such that

    ∑ j_m from 0 to l = k

    Note that k goes from z Unit.unit

    This is before RLE
  -/
  noncomputable def generatingFunction₄₀ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      ∑' (l : ℕ ), (
          (↑(Nat.factorial l ))⁻¹ • ((t • (
            Finset.sum (
             filterSequenceUpTo (z Unit.unit) (Finset.pi (Finset.range l ) (t₁ l))
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

  #eval 1 :: 2:: []
  def runLengthEncoding2 (acc : ℕ) (l : List ℕ ) : List ℕ  :=
    match l with
      | [] => (acc)::[]
      | x::xs => if x == 0 then runLengthEncoding (acc+1) xs else
        (acc) :: runLengthEncoding 0 xs

  /-
    RLE on a Finset
  -/
  def getInSet {s : Finset ℕ } (p : a+1 ∈ s) : a ∈ s := by sorry
  def zeroInSet {s : Finset ℕ } (p : 0 ∈ s) : a ∈ s := by sorry

  /-
    You need to have this take the proof that p ∈ Finset.range k

    Which then gets converted to a proof that p ∈ Finset.range l

    Which can be done by supplying the following theorem:

  -/
  def rleFin {s : Finset ℕ}
    (acc : ℕ)  (f : (a : ℕ) → a ∈ s  → ℕ) (a : ℕ) (p : a ∈ s ) : ℕ :=
    match a with
      | 0 => acc
      | a + 1 => if f a (getInSet p) == 0 then
         rleFin (acc+1) f a (getInSet p)
        else rleFin 0 f a (getInSet p)

#check Finset.card

def countOnes {s : Finset ℕ} (a acc : ℕ ) (p : size ∈ s)
  (f : (a : ℕ) → a ∈ s  → ℕ) : ℕ :=
  match a with
    | a + 1 => f acc (getInSet size p)


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


  -- Somehow we need to define our run length encoding
  -- Over a Finset of size k instead of l
  -- At the moment it takes values over l.

  #check Finset.image (λ x ↦ rleFin 0 x ) testw

  /-
    Need to convert run length encoding
    (a : ℕ ) → (a ∈ s) → ℕ
  -/
  #eval runLengthEncoding 0 [1, 0, 0, 1, 0, 1, 0, 0, 0]
  #eval runLengthEncoding 0 [0, 0, 0, 1, 0, 0, 1, 0, 0, 0]
  #eval runLengthEncoding 0 [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1]
  #eval runLengthEncoding 0 []

  /-
    Runlength encoding substitution

    Skipping down to equation 5:
  -/
  noncomputable def generatingFunction₅ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      ∑' (l : ℕ ), (
          (↑(Nat.factorial (l+(z Unit.unit)) ))⁻¹ • ((t • (
            Finset.sum (
              filterSequenceUpTo (l) (

                -- After doing rleFin we need the length
                -- Of the sequence to be k

                  Finset.image (λ x ↦ rleFin 0 x ) (
                    Finset.pi (Finset.range l ) (t₁ l)
                )

             )
            )
              (
                λ i ↦ (
                  Product₀ n ( (List.range (l ) ).attach ) (H₀*H₁) (
                    λ m ↦(m.1 ≤ (z Unit.unit), H₀*(H₁)^(
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

  #print test₀

  lemma ixSum (k l: ℕ ) (p : k ≤ l ):  ∀ f ∈ (Finset.pi (Finset.range k) (t₁ l)),
    (Finset.sum (Finset.range l).attach (λ i ↦ f i.1 (test₀ k l p i.2 ) )) = l := by sorry

  #print ixSum

  -- scoped notation "{" p "| ≤ " l "}" => Finset.range (1)

  noncomputable def generatingFunction₆ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      ∑' (l : ℕ ), (
          (t • (
            Finset.sum (

              -- This part tells us that every f adds up to l
              filterSequenceUpTo (l) (
                  Finset.image (λ x ↦ rleFin 0 x ) (
                    Finset.pi (Finset.range (z Unit.unit) ) (t₂ (z Unit.unit) (l))
                )
                -- After applying rleFin we should have a sequence of
                -- size k
             )
             -- Note that this is a sequence of size l though

            )
              (
                λ i ↦ (

                  Nat.factorial (
                    Finset.prod ((Finset.range (z Unit.unit )).attach ) (
                      λ p ↦ i p.1 (p.2)
                    )
                  )
                  • Nat.factorial (
                      Finset.sum ((Finset.range (z Unit.unit )).attach ) (
                        λ p ↦ i p.1 (p.2)
                      ) + (z Unit.unit)
                    )^(-1)
                  •
                  Product₀ n ( (List.range (z Unit.unit ) ).attach ) (H₀*H₁) (

                    λ m ↦(m.1 ≤ (z Unit.unit),
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

  /-
    Need to somehow combine summations
  -/
  noncomputable def generatingFunction₇ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      ∑' (l : ℕ ), (
          (t • (
            Finset.sum (

              -- This part tells us that every f adds up to l
              filterSequenceUpTo (l) (
                  Finset.image (λ x ↦ rleFin 0 x ) (
                    Finset.pi (Finset.range (z Unit.unit) ) (t₂ (z Unit.unit) (l))
                )
                -- After applying rleFin we should have a sequence of
                -- size k
             )
             -- Note that this is a sequence of size l though

            )
              (
                λ i ↦ (

                  Nat.factorial (
                    Finset.prod ((Finset.range (z Unit.unit )).attach ) (
                      λ p ↦ i p.1 (p.2)
                    )
                  )
                  • Nat.factorial (
                      Finset.sum ((Finset.range (z Unit.unit )).attach ) (
                        λ p ↦ i p.1 (p.2)
                      ) + (z Unit.unit)
                    )^(-1)
                  •
                  Product₀ n ( (List.range (z Unit.unit ) ).attach ) (H₀*H₁) (

                    λ m ↦(m.1 ≤ (z Unit.unit),
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

  -- def generatingFunction₁₂ (t : ℝ ) :=

  --------------------------------------

  /-
    Need to construct a function that returns
    evidence that m ∈ Finset.range (k + 1)
  -/

  noncomputable def testList {t: ℝ } {z : ℕ} (i : ℕ ): (List (Matrix (Fin n) (Fin n) ℝ )) :=
    match i with
      | 0 => []
      | (i + 1) => @testList (t) (z) i ++ [
            t • (
                  Finset.sum {H₀, H₁* (z ) } λ x ↦ x
              )
        ]
    decreasing_by
      simp_wf

  noncomputable def generatingFunction''₃ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      (Nat.factorial (z Unit.unit) )⁻¹ • (iteratedDeriv (z Unit.unit ) (
      λ _ ↦ ∑' (l : ℕ ), (
            List.prod (@testList n H₀ H₁ t (z Unit.unit) l)
          )
      ) 0)
    )

  noncomputable def generatingFunction'₃ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      (Nat.factorial (z Unit.unit) )⁻¹ • (iteratedDeriv (z Unit.unit ) (
      λ _ ↦ ∑' (l : ℕ ), (
          List.prod (@testList n H₀ H₁ t (z Unit.unit) l)
          )
      ) 0)
    )

  #check Finset.sum {
      (Finset.sum {0, 1} λ x ↦ x ),  -- J₀
      (Finset.sum {0, 1} λ x ↦ x ) -- J₁
  } λ _ ↦3

  def choices : Finset ℕ := {0, 1}
  def summation_set : Finset ℕ := {0, 1}

  /-
    Note though this enforces an ordering due to how
    this is defined.

    I need to do a Finset over the functions.

    TODO:
    Add z and t
  -/
  def testList₄  (l : ℕ ) : (Matrix (Fin n) (Fin n) ℝ ) :=
    match l with
    | 0 => Finset.sum {0,1} λ x ↦ H₀^(1-x)*(H₁)^(x)
    | l+1 => Finset.sum {0, 1} λ xₗ ↦ (testList₄ l) * H₀^(1-xₗ)*(H₁)^(xₗ)

  def testList₅ (l : ℕ ) (x : ℕ): (Matrix (Fin n) (Fin n) ℝ) :=
    match l with
    | 0 => H₀^(1-x)*(H₁)^x
    | l+1 => testList₅ l x * H₀^(1-x)*(H₁)^x

  def testList₆ (l : ℕ ) (j : ℕ → ℕ ): (Matrix (Fin n) (Fin n) ℝ) :=
    match l with
      | 0 => H₀^(1-(j l))*(H₁)^(j l)
      | l+1 => testList₆ l j * H₀^(1-(j l))*(H₁)^(j l)

  def t : ℕ → Finset ℕ
    | n => if n <= 10 then {0, 1} else ∅

  def my_set : Finset ℕ := Finset.range (10)
  def my_cart := Finset.pi my_set t
  def is_in : 0 ∈ my_set := by simp
  def my_sum : ℕ := Finset.sum my_cart (λ x ↦ x 0 (is_in))

  -- #eval my_sum
  -- syntax (priority := high) "∏"

  noncomputable def generatingFunction'₄ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      (Nat.factorial (z Unit.unit) )⁻¹ • (iteratedDeriv (z Unit.unit ) (
      λ _ ↦ ∑' (l : ℕ ), (
          @testList₄ n H₀ H₁ l
          --List.prod (@testList n H₀ H₁ t (z Unit.unit) l)
          )
      ) 0)
    )

    #check Finset.mk

    -- Create a Finite set of J₀, …, Jₗ?
    #check {2, 3}

  def my_t (a : ℕ) : Finset (ℕ ) :=
    match a with
    | 1 => {0, 1}
    | 2 => {0, 1}
    | _ => ∅

  #check (Finset.pi {1, 2, 3} my_t).val

  /-
  noncomputable def generatingFunction'₄ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ (
      (Nat.factorial (z Unit.unit) )⁻¹ • (iteratedDeriv (z Unit.unit ) (
      λ _ ↦ (
        Finset.sum {0,1} λ xₐ ↦ Finset.sum {0,1} λ xₗ↦ (∑' (l : ℕ ), (
          List.prod (@testList n H₀ H₁ t (z Unit.unit) (l-2))
              )
              * H₀^(1-xₐ)*H₁^(xₐ) * H₀^(1-xₗ)*H₁^(xₗ)
            )
          )
      ) 0)
    )
  -/

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
  theorem eqvGen' : generatingFunction'₀ = generatingFunction'₁ := by
    unfold generatingFunction'₀
    unfold generatingFunction'₁

    funext h
    rw [exp_eq_tsum]
    sorry

  #check PowerSeries.mk
  noncomputable def generatingFunction₁ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ ∑' (l : ℕ ), (
      ( (t • (H₀ + H₁ * (z Unit.unit )))^l )
  )

  theorem addToSum (z : ℕ): (H₀ + (z • H₁)) = Finset.sum {H₀, H₁*z} λ x ↦ x:= by sorry

  noncomputable def generatingFunction₂ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ ∑' (l : ℕ ), (
        ( (
          t • (
                Finset.sum {H₀, H₁* (z Unit.unit) } λ x ↦ x
              )
        )^l
      )
  )

  noncomputable def generatingFunction₃ (t: ℝ ) : PowerSeries (Matrix (Fin n) (Fin n) ℝ ) :=
    λ z ↦ ∑' (l : ℕ ), (
        (
          List.prod (@testList n H₀ H₁ t (z Unit.unit) l)
        )
      )


  -/
  /-
    Apply the derivative
  -/
  -- theorem applyDeriv₁ : generatingFunction'₁ = generatingFunction₁ := by sorry

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

  /-
  def Hᵢ (i : ℕ ) (z : ℕ ): Matrix (Fin n) (Fin n) ℝ :=
    match i with
      | 0 => H₀ * z
      | 1 => H₁ * z
      | _ => H₀ * z
  -/

  -- instance SMul : HSMul ℝ (ℕ → Matrix (Fin n) (Fin n) ℝ) := sorry

  /-
  theorem test₅ (a : ℕ ) : (λ _ ↦ a) Unit.unit = a := by
    simp

  #print test₅

  theorem test₄ (a b: ℕ) : (λ _ ↦ a) + (λ _ ↦ b) = Finset.sum ({a, b}) (·+·):=  by
    rw [Finset.sum_eq_add]
    sorry
  -/

end TimeOrderedProduct


namespace main
end main
