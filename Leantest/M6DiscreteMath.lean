import Mathlib.Tactic

namespace M6DiscreteMath

section Finsets

open Finset
variable (a b c : Finset ℕ)
variable (n : ℕ)

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  ext x; simp only [mem_inter, mem_union]; tauto

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  rw  [inter_union_distrib_left]

#check Finset.induction

example (f : ℕ → ℕ) (h : ∀ x ∈ c, f x ≠ 0) :
    ∏ x ∈ c, f x ≠ 0 := by
  induction c using Finset.induction_on with
  | empty => show 1 ≠ 0; norm_num
  | @insert a s ans ih =>
    rw [prod_insert ans]
    apply mul_ne_zero
    · apply h; simp
    apply ih
    intro x xs
    apply h
    show x ∈ insert a s
    simp; right; exact xs

/- #check Finset.min
 - #check Finset.min'
 - #check Finset.inf
 - #check Finset.inf' -/

variable {α : Type*} [Fintype α]

example : ∀ x : α, x ∈ Finset.univ := by
  intro x; exact mem_univ x

example : Fintype.card (Fin 4 × Fin 5) = 20 := by simp

end Finsets

section Counting

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α → β)
open Finset

def triangle (n : ℕ) := {p ∈ range (n + 1) ×ˢ range (n + 1) | p.1 < p.2}

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
 have ht : triangle n = (range (n + 1)).biUnion (fun j => (range j).image (., j)) := by
   ext p
   simp only [triangle, mem_filter, mem_product, mem_range, mem_biUnion, mem_image]
   constructor
   · rintro ⟨ a, b ⟩
     use p.2, a.2
     use p.1, b
   · rintro ⟨i, hi, j, hj, hij ⟩
     rw [←hij]
     omega
 rw [ht, card_biUnion]; swap
 · intro x _ y _ xney
   simp [disjoint_iff_ne]
   intros; exact xney
 transitivity (∑ i ∈ range (n + 1), i)
 · congr; ext i
   rw [card_image_of_injective, card_range]
   intro x y; simp
 rw [sum_range_id]; rfl

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n ≃ Σ i : Fin (n + 1), Fin i.val :=
    { toFun := by
        rintro ⟨ ⟨ i, j ⟩, hp ⟩
        simp [triangle] at hp
        exact ⟨ ⟨ j, hp.1.2 ⟩, ⟨ i, hp.2 ⟩ ⟩
      invFun := by
        rintro ⟨ i, j ⟩
        use ⟨ j, i ⟩
        simp [triangle]
        exact j.isLt.trans i.isLt
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl
    }
  rw [←Fintype.card_coe]
  trans; apply (Fintype.card_congr this)
  rw [Fintype.card_sigma, sum_fin_eq_sum_range]
  convert Finset.sum_range_id (n + 1)
  simp_all


example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  apply Nat.eq_div_of_mul_eq_right (by norm_num)
  show 2 * #(triangle n) = (n + 1) * n
  let turn (p : ℕ × ℕ) : ℕ × ℕ := (n - 1 - p.1, n - p.2)
  calc 2 * #(triangle n)
    _ = #(triangle n) + #(triangle n) := by
          ring
    _ = #(triangle n) + #(triangle n |>.image turn) := by
          rw [add_right_inj]
          rw [card_image_of_injOn]
          simp [turn, triangle, Set.InjOn, Function.Injective]
          omega
    _ = #(range n ×ˢ range (n + 1)) := by
          rw [←card_union_of_disjoint]; swap
          · rw [disjoint_iff_ne]
            simp [triangle, turn]; omega
          · dsimp only [triangle, turn]
            congr 1; ext x; rcases x with ⟨ i, j ⟩; constructor
            · simp; rintro (_ | _) <;> omega
            · simp;
              intro _ _
              by_cases h : (i < n + 1 ∧ j < n + 1) ∧ i < j
              · left; exact h
              right
              simp only [Decidable.not_and_iff_or_not] at h; simp at h
              rcases h with (_ | _) | _
              · omega
              · omega
              · rcases n with (_ | n); omega
                use (n - i), (n + 1 - j)
                omega
    _ = (n + 1) * n := by simp only [Finset.card_product,  Finset.card_range]; ring

open Classical
variable (s t : Finset ℕ) (a b : ℕ)

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #{b ∈ t | r a b})
    (h_right : ∀ b ∈ t, #{a ∈ s | r a b} ≤ 1) :
    3 * #(s) ≤ #(t) := by
  calc 3 * #(s)
    _ = ∑ a ∈ s, 3                               := by simp; ring
    _ ≤ ∑ a ∈ s, #{b ∈ t | r a b}                := sum_le_sum h_left
    _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := by convert sum_comm
    _ = ∑ b ∈ t, #{a ∈ s | r a b}                := by simp
    _ ≤ ∑ b ∈ t, 1                               := sum_le_sum h_right
    _ = #(t)                                     := by simp

end Counting

namespace MyList

inductive List (α : Type*) where
  | nil : List α
  | cons : α → List α → List α

end MyList

namespace InductiveTypes

open List

def append {α : Type*} : List α → List α → List α
  | [],      bs => bs
  | a :: as, bs => a :: append as bs

theorem append_nil {α : Type*} : ∀ as : List α, as ++ [] = as
  | [] => by rw [List.append_nil]
  | a :: as => by rw [cons_append, append_nil as]

variable {α : Type*}

def reverse : List α → List α := aux []
where aux rest
  | [] => rest
  | a :: as => aux (a :: rest) as

theorem reverse.aux_eq_append (as bs : List α) : reverse.aux as bs = reverse.aux [] bs ++ as := by
  induction bs generalizing as
  case nil
  · change as = [] ++ as
    rw [nil_append]
  case cons b bs ih
  · dsimp only [aux]
    nth_rw 2 [ih]
    nth_rw 1 [ih]
    rw [append_assoc, cons_append, nil_append]


theorem reverse_append (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction as
  case nil
  · nth_rw 3 [reverse]
    rw [reverse.aux]
    rw [nil_append, append_nil]
  case cons a as ih
  · rw [cons_append]
    nth_rw 3 [reverse]
    nth_rw 1 [reverse]
    simp only [reverse.aux]
    nth_rw 2 [reverse.aux_eq_append]
    nth_rw 1 [reverse.aux_eq_append]
    rw [←reverse, ih, append_assoc]

theorem reverse_reverse (as : List α) : reverse (reverse as) = as := by
  induction as
  · rfl
  case cons a as ih
  calc reverse (reverse (a :: as))
    _ = reverse (reverse ([a] ++ as)) := by rw [cons_append, nil_append]
    _ = reverse (reverse as ++ reverse [a]) := by rw [reverse_append]
    _ = reverse (reverse [a]) ++ reverse (reverse as) := by rw [reverse_append]
    _ = a :: reverse (reverse as) := by rfl
    _ = a :: as := by rw [ih]

inductive BinTree where
  | empty : BinTree
  | node  : BinTree → BinTree → BinTree

namespace BinTree

def size : BinTree → ℕ
  | empty    => 0
  | node l r => size l + size r + 1

def depth : BinTree → ℕ
  | empty    => 0
  | node l r => max (depth l) (depth r) + 1

theorem size_le : ∀ t : BinTree, size t ≤ 2^depth t - 1
  | empty => Nat.zero_le _
  | node l r => by
    dsimp only [depth, size]
    calc l.size + r.size + 1
    _ ≤ (2^l.depth - 1) + (2^r.depth - 1) + 1 := by
      /- gcongr tactic is so convenient -/
      gcongr <;> apply size_le
    _ ≤ (2^max l.depth r.depth - 1) + (2^max l.depth r.depth - 1) + 1 := by
      gcongr <;> simp
    _ ≤ 2 ^ (max l.depth r.depth + 1) - 1 := by
      have : 0 < 2 ^ max l.depth r.depth := by simp
      omega

theorem depth_le_size : ∀ t : BinTree, depth t ≤ size t
  | empty => Nat.zero_le _
  | node l r => by
    dsimp only [depth, size]
    have := depth_le_size l
    have := depth_le_size r
    omega

def flip : BinTree → BinTree
  | empty => empty
  | node l r => node (flip r) (flip l)

theorem size_flip : ∀ t, size (flip t) = size t
  | empty => rfl
  | node l r => by
    have := size_flip l
    have := size_flip r
    dsimp [flip, size]
    linarith

example : flip  (node (node empty (node empty empty)) (node empty empty)) =
    node (node empty empty) (node (node empty empty) empty) := by rfl

end BinTree
end InductiveTypes

section Eval

inductive PropForm : Type where
  | var (n : ℕ)           : PropForm
  | fls                   : PropForm
  | conj (A B : PropForm) : PropForm
  | disj (A B : PropForm) : PropForm
  | impl (A B : PropForm) : PropForm
open PropForm

def eval : PropForm → (ℕ → Bool) → Bool
  | var n, v => v n
  | fls, _ => false
  | conj a b, v => eval a v && eval b v
  | disj a b, v => eval a v || eval b v
  | impl a b, v => ! eval a v || eval b v

def vars : PropForm → Finset ℕ
  | var n => {n}
  | fls => ∅
  | conj a b => vars a ∪ vars b
  | disj a b => vars a ∪ vars b
  | impl a b => vars a ∪ vars b

theorem eval_eq_eval (a : PropForm) : (v1 v2 : ℕ → Bool) →
    (∀ n ∈ vars a, v1 n = v2 n) → eval a v1 = eval a v2 := by
  induction a
  · simp [vars, eval]
  · simp [eval]
  all_goals
    simp [vars, eval]
    grind

def subst : PropForm → ℕ → PropForm → PropForm
  | var n, m, c => if n = m then c else var n
  | fls, _, _  => fls
  | conj a b, m, c => conj (subst a m c) (subst b m c)
  | disj a b, m, c => disj (subst a m c) (subst b m c)
  | impl a b, m, c => impl (subst a m c) (subst b m c)

#eval subst (conj (var 0) (var 1)) 0 (var 1)  /- :clown: -/

theorem subst_eq_of_not_mem_vars (a : PropForm)
    : (n : ℕ) → (c : PropForm) → n ∉ vars a → subst a n c = a := by
  induction a; swap
  all_goals
    simp [vars, subst]
    try tauto

theorem subst_eval_eq (a : PropForm)
    : ∀ (n : ℕ) (c : PropForm) (v : ℕ → Bool),
      eval (subst a n c) v = eval a (fun m => if m = n then eval c v else v m) := by
  induction a
  case var n =>
    intro m _ _
    by_cases h : n = m <;> simp [eval, subst]
    · simp [if_pos h]
    · simp [if_neg h, eval]
  case fls =>
    simp [eval, subst]
  all_goals
    intro m _ _
    simp [eval, subst]
    grind

end Eval
end M6DiscreteMath
