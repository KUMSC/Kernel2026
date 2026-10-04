import Mathlib


#eval 2+2
#eval "Hello"

#check 67
#check "hello"
#check 2<1

def roll_no : ℕ := -1

def double (n:ℕ) := n+n
def square (n:ℕ  ) := n*n 
-- theorem <name> : <proposition> := <proof>

theorem about_2 : double 2 = square 2 := by rfl

example (P: Prop): P → P := by
  intro h
  exact h

example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact And.left h

example (P Q : Prop) : P ∨ Q →  Q ∨ P := by
  intro h
  cases h with 
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

#check And.left -- P ∧ Q → P
#check And.right -- P ∧ Q → Q
#check Or.inl -- P → P ∨ Q
#check Or.inr -- Q → P ∨ Q

example (P Q : Prop) : P → Q → Q := by 
  intro h1 h2
  exact h2







example (P Q : Prop) (h1: P) (h2:Q) : P∧ Q := by 
  constructor
  exact h1
  exact h2





example : 2*2 = 4 := by rfl

#check ∀n:ℕ , n+1>n

theorem th1 (P Q :Prop) : P ∧   Q := sorry

theorem th2 : ∀n:ℕ , n+1>n := sorry
theorem th3 : ∃k:ℕ , k=7 := sorry
theorem th4 (P Q :Prop) (h: P → Q) : Q := sorry


example (P Q :Prop) : Q → P ∨ Q := sorry
example  : ∀ n : ℕ  , ∃ m:ℕ , m > n := sorry


example (P Q R: Prop) (p: P)(q:Q)(h1: P → Q) (h2: Q→R):  (P→R) := by
  intro h
  apply h2 (h1 h)
--similar to function composition



--definition
def isEven (n:ℕ) : Prop := ∃ k : ℕ, n = 2*k

theorem twenty: isEven 20 := by 
  unfold isEven 
  let k := 10
  use k
  calc 20 = 2 *k := rfl

theorem e6 : isEven 6 := by
  unfold isEven
  use 3

theorem even_sum_even (n m : ℕ ): (isEven n) ∧ (isEven m) → isEven (n+m) := by
  intro h
  have h1: isEven n := And.left h
  unfold isEven at h1
  obtain ⟨k, h1' ⟩ := h1 

  have h2: isEven m := And.right h
  unfold isEven at h2
  obtain ⟨l, h2' ⟩ := h2

  unfold isEven 
  use k+l
  calc n+m = 2*k + 2*l := by rw[h1', h2']
   _ = 2*(k+l) := by rw [←  Nat.left_distrib 2 k l]


#check Nat.left_distrib



  

    
