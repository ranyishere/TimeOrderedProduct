import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Ring.Pi
import Mathlib.Data.Real.Basic

namespace Example

  open Finset
  open BigOperators

  def s : Finset Nat := {1, 2, 3}

  def t (a : Nat) : Finset Nat :=
    match a with
      | 1 => {1, 2}
      | 2 => {3, 4}
      | 3 => {5, 6}
      | _ => ∅

  def check_finset := Finset.pi s t
  #print s
  #print check_finset
  #print Finset.pi
  #print Multiset.pi


  def f (a b : Nat) : Nat := a * b

  -- Applying the prod_sum theorem
  theorem check : (∏ a in s, ∑ b in t a, f a b) = ∑ p in s.pi t, ∏ x in s.attach, f x.1 (p x.1 x.2) := by
  rw [prod_sum]

end Example

namespace TestingRing
  def f (n : ℕ) : ℤ := n * 2  -- Example: f(n) = 2n
  def g (n : ℕ) : ℤ := n + 1  -- Example: g(n) = n + 1
  def together := (f + g)
end TestingRing

/-
  Let's define sequences
-/
namespace Sequence

  -- inductive

  -- Our type
  def Sequence (α : Type _ ) := ℕ → α

  def mkSequence (α : Type _) := Sequence α

  -- Empty Sequence
  instance [Inhabited α] : EmptyCollection (Sequence α) where
    emptyCollection := fun _ => default

  -- Sequence membership
  instance [DecidableEq α] : Membership α (Sequence α) where
    mem a seq := ∃ n : ℕ, seq n = a

  -- Probably define induction using Nat.rec
  /-
  def induction {α : Type _} (seq : Sequence α) (p : ℕ → Sequence α → Prop )
    (base : P )
    : ∀ (n : ℕ), p n seq → p (n + 1) seq :=
    Nat.rec
  -/

  def mySequence (i : ℕ) : ℕ  :=
    match i with
      | _ => 2

  def NatSequence : Sequence ℕ := mySequence

  #check 2 ∈ NatSequence

  #check Exists.intro

  theorem check₅ : NatSequence 2 = 2 := by
    simp

  -- Proving that 2 ∈ NatSequence
  theorem check₄ : 2 ∈ NatSequence :=
    ⟨_, check₅⟩

  -- theorem check₇ (a : ℕ ): NatSequence a ≠ 3 := by
  -- intro h

  -- theorem check₆ (a : ℕ): (3 ∉ NatSequence) ↔ (NatSequence a ≠ 3 ) := by

  /-
   Sum
  -/
  def sum [Semiring β] {α : Type _} (seq : Sequence α ) (start : ℕ ) (stop : ℕ ) (f : α → β ): β :=
    if start > stop then 0
    else f (seq (start)) + sum seq (start + 1) (stop) f
    decreasing_by sorry

  def empty_sum [Semiring β] {α : Type _ } (seq : Sequence α) (f: α → β) : sum seq 1 0 f = 0 := by
    unfold sum
    rfl

  def ident_sum [Semiring β] {α : Type _} (seq : Sequence α) (f: α → β ) : sum seq 0 0 f = f (seq 0) := by
    unfold sum
    simp
    rw [empty_sum]
    simp

  /-
    Prod
  -/
  def prod [Semiring β] {α  : Type _} (seq : Sequence α )
    (start : ℕ ) (stop : ℕ ) (f : α → β): β :=
    if start > stop then 1
    else f (seq start) * prod seq (start + 1) (stop) f
    decreasing_by
    simp_wf

  theorem empty_prod [Semiring β] {α : Type _ } (seq : Sequence α)
    (f : α → β ): prod seq 1 0 f = 1 := by

    unfold prod
    simp

  theorem ident_prod [Semiring β] {α : Type _ } (seq : Sequence α)
    (f : α → β ): prod seq 0 0 f = f (seq 0) := by

    unfold prod
    simp
    rw [empty_prod]
    simp

  /-
    ∏ ∑ f = ∑ f(x₀) when you product size min is 0 and product max is 1
  -/
  theorem empty_prod_sum [Semiring β] {α : Type _} (seq₀ seq₁: Sequence α)
    (j k: ℕ ) (f : α → β) : prod seq₀ 0 0 (λ x ↦ sum seq₁ j k (λ _ ↦ (f x)) )
    = sum seq₁ j k (λ _ ↦ (f (seq₀ 0))) := by

    unfold prod
    rw [empty_prod]
    simp

  /-
    ∑ ∏ f = ∏ f(x₀)
  -/
  theorem empty_sum_prod [Semiring β] {α : Type _} (seq₀ seq₁ : Sequence α )
    (j k : ℕ ) (f : α → β) : sum seq₀ 0 0 (λ x ↦ prod seq₁ j k (λ _ ↦(f x) )) = prod seq₁ j k (λ _ ↦(f (seq₀ 0)) ) := by

      unfold sum
      rw [empty_sum]
      simp

  def empty_pi {α : Type _} {δ : α → Sort _} : ∀ a ∈ emptyCollection, δ a := fun .

  /-
   Pi Type -> Cartesian Product of Sequence with natural number
              {(1, seq₁), (1, seq₂), … ,(2, seq₁), (2, seq₂), …, (n, seqₙ)}

              This is the same as just defining a sequence from 1 to N
              and returning the sequence:

              λ n ↦ seqₙ
  -/

  -- We need to define the cartesian product over sequences to
  -- adequately define pi types
  def pi {α :Type _ } {δ : α → Type _ } (seq : Sequence α )
         (t : (a: α) → Sequence (δ a) )
         : Sequence (∀a, δ a) :=
         _


  -- Cartesian Product between sequences.

  -- def pi {α : Type _} {δ : α → Type _} (seq : Sequence α) (t : (a: α) → Sequence (δ a)) : Sequence (∀a, δ a) :=
  -- λ n, λ a, (t a) n

  -- def Pi.empty {α : Type _} {δ : α → Sort _ } (empty_seq : Sequence α) : ∀ a, δ (empty_seq a)   :=
    -- fun.

  -- Grab each element in my sequence and pass it to delta
  -- λ n ↦ (λ y ↦ t (y) n)
  def pi {α :Type _ } {δ : α → Type _ } (seq : Sequence α )
         (t : (a: α) → Sequence (δ a) ) (start : ℕ) (stop : ℕ)
         : Sequence (∀a, δ a) := λ n ↦ λ a ↦ (t a) n

  -- This works, how do we generalize this?
  def pi' {α :Type _ } (seq : Sequence α ) (t : (a: α) → Sequence ( Sequence ℕ ) ) : Sequence (Sequence ℕ ) :=
  λ n ↦ t (seq n) n


  def pi'' {α : Type _} (seq : Sequence α) (t : (a : α) → )

  def pi_3 [DecidableEq α] {β : α → Type u} (m : Multiset α) (t : ∀ a, Multiset (β a)) : Multiset (∀ a ∈ m, β a) :=

    m.recOn {Multiset.Pi.empty β}
      (fun a m (p : Multiset (∀ a ∈ m, β a)) => (t a).bind fun b => p.map <| Multiset.Pi.cons m a b)
      (byA Playthrough of a Certain Dude's VRMMO Life
        intro a a' m n
        by_cases eq : a = a'
        · subst eq; rfl
        · simp [Multiset.map_bind, Multiset.bind_bind (t a') (t a)]
          apply Multiset.bind_hcongr
          · rw [Multiset.cons_swap a a']
          intro b _
          apply Multiset.bind_hcongr
          · rw [Multiset.cons_swap a a']
          intro b' _
          apply Multiset.map_hcongr
          · rw [Multiset.cons_swap a a']
          intro f _
          exact Multiset.Pi.cons_swap eq)

  -- def pi_2 {α :Type _ } {δ : α → Type _ } (seq : Sequence α ) (t : (a: α) → Sequence ( δ a ) ) : Sequence ((a : ℕ ) →  δ (seq a) ) := by
  -- induction' seq

  /-
    Define f here
  -/
  def f (a b : ℕ) := a * b

  def t (a : ℕ ) : Sequence (Sequence ℕ) :=
    match a with
    | _ => λ x ↦ (λ y ↦ ( x + y))

  def t' (a : ℕ ) : Sequence ( ℕ ) :=
    match a with
    | 1 => λ _ ↦ 1
    | 2 => λ _ ↦ 2
    | 3 => λ _ ↦ 3
    | 4 => λ _ ↦ 4
    | _ => ∅


  -- Cartesian product of the sequences

  def x₀ := 0
  def x₁ := 1
  def x₂ := 2

  -- Same here
  #eval prod NatSequence (0) (1) (λ x ↦ (sum (t x) (0) (0) (λ y ↦f x (y x))))
  #eval sum (pi' (NatSequence) t) (0) (0) (λ x ↦ prod (NatSequence) 0 1 (λ y ↦ f y (x y) ))

  -- Difference
  #eval prod NatSequence (0) (1) (λ x ↦ (sum (t x) (0) (1) (λ y ↦f x (y x))))
  #eval sum (pi' (NatSequence) t) (0) (1) (λ x ↦ prod (NatSequence) 0 1 (λ y ↦ f y (x y) ))

  /-
    #eval f 2 4
    #eval (t x₀) (0) (2)
    #eval (t x₁) (0) (2)
    #eval (sum (t x₁) (1) (1) (λ y ↦f x₁ (y x₁)))
    #eval (sum (t x₂) (0) (1) (λ y ↦f x₂ (y x₂)))
  -/

  #eval prod NatSequence (0) (1) (λ x ↦ (sum (t x) (0) (1) (λ y ↦f x (y x))))


  theorem test₅ : prod NatSequence (0) (1) (λ x ↦ (sum (t x) (0) (1) (λ y ↦f x (y x)))) = 100 := by
  unfold prod
  unfold prod
  unfold sum
  unfold sum
  unfold f
  unfold t
  simp

  #eval sum (pi' (NatSequence) t) (0) (1) (λ x ↦ prod (NatSequence) 0 1 (λ y ↦ f y (x y) ))
  #eval t 4 0 0

  def test₄ : prod NatSequence (0) (1) (λ x ↦ (sum (t x) (0) (1) (λ y ↦f x (y x))))
  = sum (pi' (NatSequence) t) (0) (1) (λ x ↦ prod (NatSequence) 0 1 (λ y ↦ f y (x y) ))
  → false := by

    unfold prod
    simp

    unfold sum
    simp

    unfold f
    unfold t
    simp

    unfold NatSequence
    unfold mySequence
    simp

    unfold sum
    unfold prod
    unfold sum

    unfold pi'

    simp

  -- TODO: Get these to become equivalent, and why arent they
  --       Equivalent?
  #eval prod NatSequence (0) (1) (λ x ↦ (sum (t x) (0) (1) (λ y ↦f x (y x))))
  -- The above evaluates to 100

  #eval sum (pi' (NatSequence) t) (0) (1) (λ x ↦ prod (NatSequence) 0 1 (λ y ↦ f y (x y) ))
  -- The above evaluates to 52

  -- prod first
  #eval sum (t x₁) (0) (1) (λ y ↦f x₁ (y x₁))
  #eval sum (t x₁) (0) (1) (λ y ↦f 2 (y 2))

  -- sum first
  def initₚ := (pi' (NatSequence) t) 0
  #eval (pi' (NatSequence) t) 0 1
  #eval prod (NatSequence) 0 1 (λ y ↦ f y (initₚ  y) )
  #eval sum (pi' (NatSequence) t) (0) (1) (λ x ↦ prod (NatSequence) 0 1 (λ y ↦ f y (x y) ))

  /- TODO: Need to define this over f that are not just over natural numbers
           Probably define this over another type β with some nice
           property such as Ring
  -/
  theorem prod_sum {δ: α → Type _ } {seq : Sequence α}
                   {t: (a: α) → Sequence (δ a)} {f: (a: α) → (δ a) → ℕ}
                   (lower_bound_prod : ℕ)  (upper_bound_prod : ℕ)
                   (lower_bound_sum : ℕ) (upper_bound_sum : ℕ) :
    (prod seq (lower_bound_prod) (upper_bound_prod)
      (λ x ↦ (sum (t x) lower_bound_sum upper_bound_sum (λ y ↦ f x y )))
    )
    = (sum (pi (seq) t) (lower_bound_sum) (upper_bound_sum)
       (λ x ↦ (prod seq lower_bound_prod upper_bound_prod (λ y ↦ f y (x y))) )
    ) := by
    induction upper_bound_prod
    unfold prod
    simp
    unfold sum
    simp

  #check prod_sum

  def seq₁ { α : Type _} {x : α } [Semiring α] : Sequence α := fun _ => x
  def seq₂ { α : Type _} {y : α } [Semiring α] : Sequence α := fun _ => y

  #check sum (@seq₁ ℕ )  1 10


-- #eval sum (NatSequence) (0) (10)

end Sequence
