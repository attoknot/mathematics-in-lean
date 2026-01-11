import Mathlib.Topology.Basic
import Init.Data.Nat.Lemmas
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Divisibility.Basic

example (a b c : ℕ) : a * b * c = b * (a * c) := by
  rw [Nat.mul_comm a b]
  rw [Nat.mul_assoc b a c]

example (a b c : ℕ) : min a b = c → (a = c ∨ b = c) := by
  intro h
  rw [min_def] at h
  by_cases h2 : (a ≤ b)
  · rw [if_pos h2] at h
    left
    exact h
  · rw [if_neg h2] at h
    right
    exact h


example (a b c : ℕ) : a * (b * c) = b * (a * c) := by
  rw [←Nat.mul_assoc a b c]
  rw [←Nat.mul_assoc b a c]
  rw [Nat.mul_comm b a]

example (a b c d : ℕ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp', Nat.mul_comm, Nat.sub_self] at hyp
  exact hyp

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  calc
    _ = a * a + b * a - (a * b + b * b) := by rw [mul_sub, add_mul, add_mul]
    _ = a * a + b * a + (- (a * b + b * b)) := by rw [sub_eq_add_neg]
    _ = a * a + (- (a * b + b * b)) + b * a := by rw [add_assoc, add_comm (b * a), ←add_assoc]
    _ = a * a + (- (a * b) + - (b * b)) + b * a := by rw [neg_add]
    _ = a * a + (- (b * b) + - (a * b)) + b * a := by rw [add_comm (- (a * b))]
    _ = a * a + - (b * b) + (- (a * b) + b * a) := by rw [←add_assoc, add_assoc _ _ (b * a)]
    _ = a * a + - (b * b) := by rw [mul_comm a b, add_comm _ (b * a), add_neg_cancel, add_assoc, add_zero]
    _ = a ^ 2 - b ^ 2 := by rw [←pow_two, ←pow_two, ←sub_eq_add_neg]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [←add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm b, neg_add_cancel, add_zero]

theorem add_right_cancel (a b c : R) (h : a + b = c + b) : a = c := by
  rw [←add_zero a, ←neg_add_cancel b, ←add_comm b, ←add_assoc]
  rw [h, add_assoc, add_comm b, neg_add_cancel, add_zero c]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [add_comm a b, add_comm a c] at h
  apply (add_right_cancel b a c h)

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [←mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    rw [←add_mul, zero_add, zero_add]
  rw [add_right_cancel _ _ _ h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [←add_zero b, ←neg_add_cancel a]
  rw [←add_assoc, add_comm b, add_assoc, add_comm b]
  rw [h, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [add_comm] at h
  rw [neg_eq_of_add_eq_zero h]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  apply neg_add_cancel

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, ←add_neg_cancel a]

theorem two_mul (a : R) : 2 * a = a + a := by
  have h : (2 : R) = 1 + 1 := by norm_num
  rw [h, add_mul, one_mul]

end MyRing

namespace MyGroup

variable {G : Type*} [Group G]

theorem my_mul_cancel_left (a b c : G) (h : a * b = a * c) : b = c := by
  have h2 : a⁻¹ * a * b = a⁻¹ * a * c := by rw [mul_assoc, mul_assoc, h]
  rw [inv_mul_cancel, one_mul, one_mul] at h2
  exact h2

theorem my_mul_one (a : G) : a * 1 = a := by
  rw [←inv_mul_cancel a]
  apply my_mul_cancel_left (a⁻¹)
  rw [←mul_assoc, inv_mul_cancel, one_mul]

theorem my_inv_inv (a : G) : a⁻¹ ⁻¹ = a := by
  have h1 : a⁻¹ ⁻¹ * a⁻¹ * a = a := by rw [inv_mul_cancel (a⁻¹), one_mul]
  have h2 : a⁻¹ ⁻¹ * a⁻¹ * a = a⁻¹ ⁻¹ := by rw [mul_assoc, inv_mul_cancel a, my_mul_one]
  rw [h2] at h1
  exact h1

theorem my_mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  nth_rw 1 [←my_inv_inv a, inv_mul_cancel]

example (a b c d e : ℕ) (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀
  apply lt_trans h₁
  apply lt_of_le_of_lt h₂
  exact h₃

end MyGroup

open Real
example (a b c : ℝ) (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply sub_le_sub ; apply le_rfl
  apply exp_le_exp.mpr h
  
theorem mul2_le_sqs (a b : ℝ) : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2 := by calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
theorem negmul2_le_sqs (a b : ℝ) : -2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 + 2*a*b + b^2 := by calc
    a^2 + 2*a*b + b^2 = (a + b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
       
example (a : ℝ) : |a*b| ≤ (a^2 + b^2)/2 := by
  apply abs_le'.mpr ; constructor
  · linarith [mul2_le_sqs a b]
  · linarith [negmul2_le_sqs a b]

example (a b : ℕ) : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

example (a b c : ℕ) : min (min a b) c = min a (min b c) := by

  apply le_antisymm <;> apply le_min <;> try apply le_min
    <;> (try apply min_le_left) <;> (try apply min_le_right)
  · apply le_trans
    · apply min_le_left
    · apply min_le_left
  · apply le_trans
    · apply min_le_left
    · apply min_le_right
  · apply le_trans
    · apply min_le_right
    · apply min_le_left
  · apply le_trans
    · apply min_le_right
    · apply min_le_right

theorem aux (a b c : ℕ) : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min <;> apply add_le_add
    <;> (try apply min_le_left) <;> (try apply min_le_right)
    <;> apply le_rfl

example (x y z : ℕ) (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example (x y z w : ℕ) (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply (Nat.dvd_add_right _).mpr
  · apply dvd_trans h
    apply dvd_mul_left
  apply (Nat.dvd_add_right _).mpr
  · apply dvd_mul_left
  · apply dvd_mul_of_dvd_right
    apply dvd_mul_right

example (n m : ℕ) : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  · apply (dvd_gcd_iff _ _ _).mpr ; constructor
    · apply gcd_dvd_right
    · apply gcd_dvd_left
  · apply (dvd_gcd_iff _ _ _).mpr ; constructor
    · apply gcd_dvd_right
    · apply gcd_dvd_left


namespace AlgebraicStructures

variable {α : Type*} [Lattice α]
variable (x y z : α)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    · exact inf_le_right
    · exact inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm <;> apply le_inf <;> try apply le_inf
  all_goals (try apply inf_le_left) ; (try apply inf_le_right)
  apply le_trans inf_le_left inf_le_left
  apply le_trans inf_le_left inf_le_right
  apply le_trans inf_le_right inf_le_left
  apply le_trans inf_le_right inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    · exact le_sup_right
    · exact le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm <;> apply sup_le <;> try apply sup_le
  all_goals (try apply le_sup_left); (try apply le_sup_right)
  apply le_trans le_sup_right; rw [sup_comm]; apply le_sup_right
  apply le_trans le_sup_right le_sup_right
  apply le_trans le_sup_left le_sup_left
  apply le_trans le_sup_left; rw [sup_comm]; apply le_sup_left

example : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf le_rfl le_sup_left

example : x ⊔ (x ⊓ y) = x := by
  apply le_antisymm
  · apply sup_le le_rfl inf_le_left
  · apply le_sup_left

variable (a b c : α)

example : (a ⊔ a) = a := by
  apply le_antisymm
  · apply sup_le le_rfl le_rfl
  · apply le_sup_left

/- this was outrageous -/
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
 symm
 calc (a ⊔ b) ⊓ (a ⊔ c)
   _ = (a ⊔ b) ⊓ a ⊔ (a ⊔ b) ⊓ c := by rw [h]
   _ = a ⊓ (a ⊔ b) ⊔ c ⊓ (a ⊔ b) := by rw [inf_comm _ a, inf_comm _ c]
   _ = (a ⊓ a) ⊔ (a ⊓ b) ⊔ (c ⊓ a) ⊔ (c ⊓ b) := by rw [h, h, ←sup_assoc]
   _ = (a ⊔ a ⊓ b) ⊔ (a ⊔ c ⊓ a) ⊔ (c ⊓ b) := by nth_rw 1 [inf_idem a, ←sup_idem a, sup_assoc a, sup_comm a, sup_assoc _ a]
   _ = a ⊔ a ⊔ (c ⊓ b) := by rw [sup_inf_self, inf_comm c a, sup_inf_self]
   _ = a ⊔ (b ⊓ c) := by rw [sup_idem, inf_comm]

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

example (h : a ≤ b) : 0 ≤ b - a := by
  rw [←neg_add_cancel a, add_comm, sub_eq_neg_add, add_comm _ b]
  apply add_le_add_left h

example (h : 0 ≤ b - a) : a ≤ b := by
  rw [←neg_add_cancel a, add_comm, sub_eq_neg_add, add_comm _ b] at h
  rw [←add_zero a, ←add_zero b, ←neg_add_cancel a, ←add_assoc, ←add_assoc]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  by_cases hc : (c = 0)
  · rw [hc, mul_zero, mul_zero]
  by_cases hab : (a = b)
  · rw [hab]
  apply le_of_lt_or_eq ; left
  apply mul_lt_mul_of_pos_right
  · apply lt_of_le_of_ne h hab
  · apply lt_of_le_of_ne h'
    symm; exact hc

end AlgebraicStructures

namespace AlgebraicStructures2

variable {X : Type*} [MetricSpace X]
variable (x y z : X)

example (x y : X) : 0 ≤ dist x y := by
  have h : 0 ≤ dist x y + dist x y := by
    rw [←dist_self x]
    nth_rw 2 [dist_comm x y]
    apply dist_triangle
  rw [←mul_two] at h
  apply nonneg_of_mul_nonneg_left h
  linarith

end AlgebraicStructures2
