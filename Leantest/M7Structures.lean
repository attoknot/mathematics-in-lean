import Mathlib.Tactic

namespace M7Structures

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext

def Point1 : Point where
  x := 2
  y := 3
  z := -4

def myPoint2 : Point := ⟨ 2, 3, -4 ⟩

namespace Point

def add (a b : Point) : Point :=
  ⟨ a.x + b.x, a.y + b.y, a.z + b.z ⟩

#check Point1.x

protected theorem add_comm (a b : Point) : add a b = add b a := by
  dsimp only [add]
  ext <;> dsimp <;> rw [add_comm]

def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  dsimp only [addAlt]
  ext <;> dsimp <;> rw [add_comm]

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  dsimp only [add]
  ext <;> dsimp <;> rw [add_assoc]

def smul (r : ℝ) (p : Point) : Point :=
  ⟨ r * p.x, r * p.y, r * p.z ⟩

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
  dsimp only [smul, add]
  ext <;> dsimp <;> rw [mul_add]

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

def swap_xy (a : StandardTwoSimplex) : StandardTwoSimplex where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

noncomputable section

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2

  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

def weighted_nonneg {k a b : ℝ} : 0 ≤ k → k ≤ 1 → 0 ≤ a → 0 ≤ b → 0 ≤ k * a + (1 - k) * b := by
  intros _ _ _ _
  have : 0 ≤ 1 - k := by linarith
  apply add_nonneg <;> apply mul_nonneg <;> assumption
  
def weightedAverage (k : ℝ) (k_nonneg : 0 ≤ k) (k_le : k ≤ 1)
    (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := k * a.x + (1 - k) * b.x
  y := k * a.y + (1 - k) * b.y
  z := k * a.z + (1 - k) * b.z

  x_nonneg := weighted_nonneg k_nonneg k_le a.x_nonneg b.x_nonneg
  y_nonneg := weighted_nonneg k_nonneg k_le a.y_nonneg b.y_nonneg
  z_nonneg := weighted_nonneg k_nonneg k_le a.z_nonneg b.z_nonneg
  sum_eq := by calc
    _ = k * (a.x + a.y + a.z) + (1 - k) * (b.x + b.y + b.z) := by ring
    _ = 1 := by rw [a.sum_eq, b.sum_eq]; ring

open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n where
  V i := (a.V i + b.V i) / 2
  NonNeg i := by linarith [a.NonNeg i, b.NonNeg i]
  sum_eq_one := by
    simp [div_eq_mul_inv, ←Finset.sum_mul, Finset.sum_add_distrib]
    rw [a.sum_eq_one, b.sum_eq_one]
    ring

def weightedAverage (n : ℕ) (k : ℝ) (k_nonneg : 0 ≤ k) (k_le : k ≤ 1) (a b : StandardSimplex n) : StandardSimplex n where
  V i := k * a.V i + (1 - k) * b.V i
  NonNeg i := by
    have := a.NonNeg i
    have := b.NonNeg i
    have : 0 ≤ 1 - k := by linarith
    apply add_nonneg <;> apply mul_nonneg <;> assumption
  sum_eq_one := by
    rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum]
    rw [a.sum_eq_one, b.sum_eq_one]
    ring

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

namespace AnonymousStructures

def Point := ℝ × ℝ × ℝ
def IsLinear (f : ℝ → ℝ) := (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x
def PReal := { y : ℝ // 0 ≤ y }

def StandardTwoSimplex :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }
def StandardSimplex' := Σ n : ℕ, StandardSimplex n

end AnonymousStructures

class Mygroup (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

structure MyAddGroup (α : Type*) where
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add zero x = x
  neg_add_cancel : ∀ x : α, add (neg x) x = zero

namespace Point

def neg (a : Point) : Point where
  x := -a.x
  y := -a.y
  z := -a.z

def zero : Point := ⟨ 0, 0, 0 ⟩

def addGroupPoint : MyAddGroup Point where
  add := add
  zero := zero
  neg := neg
  add_assoc x y z := by simp only [add, add_assoc]
  add_zero x := by simp only [add, zero, add_zero]
  zero_add x := by simp only [add, zero, zero_add]
  neg_add_cancel x := by simp only [add, zero, neg, neg_add_cancel]

instance {α : Type*} : Mygroup (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc _ _ _ := (Equiv.trans_assoc _ _ _).symm
  mul_one := Equiv.trans_refl
  one_mul := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm

def mySquare {α : Type*} [Mygroup α] (x : α) := Mygroup.mul x x

instance : Inhabited Point where default := zero
example : ([] : List Point).headI = default :=
  rfl

instance : Add Point where add := add
example (x y : Point) : x + y = x.add y :=
  rfl

instance {α : Type*} [Mygroup α] : Mul α := ⟨ Mygroup.mul ⟩
instance {α : Type*} [Mygroup α] : One α := ⟨ Mygroup.one ⟩
instance {α : Type*} [Mygroup α] : Inv α := ⟨ Mygroup.inv ⟩

section
variable {α : Type*} (f g : Equiv.Perm α)
#check f * 1 * g⁻¹
end

end Point
end StandardSimplex
end
end Point

namespace GaussianIntegers

@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ

instance : Zero GaussInt :=
  ⟨ ⟨ 0, 0 ⟩ ⟩
instance : One GaussInt :=
  ⟨ ⟨ 1, 0 ⟩ ⟩
instance : Add GaussInt :=
  ⟨ fun x y => ⟨ x.re + y.re, x.im + y.im ⟩ ⟩
instance : Neg GaussInt :=
  ⟨ fun x => ⟨ -x.re, -x.im ⟩ ⟩
instance : Mul GaussInt :=
  ⟨ fun x y => ⟨ x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re ⟩ ⟩

namespace GaussInt

theorem zero_def : (0 : GaussInt) = ⟨ 0, 0 ⟩ := rfl
theorem one_def : (1 : GaussInt) = ⟨ 1, 0 ⟩ := rfl
theorem add_def (x y : GaussInt) : x + y = ⟨ x.re + y.re, x.im + y.im ⟩ := rfl
theorem neg_def (x : GaussInt) : -x = ⟨ -x.re, -x.im ⟩ := rfl
theorem mul_def (x y : GaussInt) : x * y = ⟨ x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re ⟩ := rfl

@[simp]
theorem zero_re : (0 : GaussInt).re = 0 := rfl
@[simp]
theorem zero_im : (0 : GaussInt).im = 0 := rfl
@[simp]
theorem one_re : (1 : GaussInt).re = 1 := rfl
@[simp]
theorem one_im : (1 : GaussInt).im = 0 := rfl
@[simp]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re := rfl
@[simp]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im := rfl
@[simp]
theorem neg_re (x : GaussInt) : (-x).re = -x.re := rfl
@[simp]
theorem neg_im (x : GaussInt) : (-x).im = -x.im := rfl
@[simp]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re := rfl

instance : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_assoc := by intros; ext <;> simp <;> ring
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  zero_mul := by intros; ext <;> simp
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  mul_assoc := by intros; ext <;> simp <;> ring
  mul_comm := by intros; ext <;> simp <;> ring
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring

instance : Nontrivial GaussInt := by
  use 0, 1
  intro h
  rw [GaussInt.ext_iff] at h
  contradiction

def div' (a b : ℤ) :=
  (a + b / 2) / b

def mod' (a b : ℤ) :=
  (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
  rw [div', mod']
  linarith [Int.mul_ediv_add_emod (a + b / 2) b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |mod' a b| ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  · linarith [Int.emod_nonneg (a + b / 2) h.ne']
  have := Int.emod_lt_of_pos (a + b / 2) h
  have := Int.mul_ediv_add_emod b 2
  have := Int.emod_lt_of_pos b zero_lt_two
  linarith

theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]

theorem sq_add_sq_eq_zero {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (x y : α) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · have := sq_nonneg x
    have := sq_nonneg y
    intro h
    have : x ^ 2 = 0 := by grind
    have : y ^ 2 = 0 := by grind
    simp only [pow_two, mul_eq_zero] at *
    tauto
  · rintro ⟨ rfl, rfl ⟩
    simp


def norm (x : GaussInt) :=
  x.re ^ 2 + x.im ^ 2

@[simp]
theorem norm_nonneg (x : GaussInt) : 0 ≤ norm x := by
  rw [norm]
  linarith [sq_nonneg x.re, sq_nonneg x.im]

theorem norm_eq_zero (x : GaussInt) : 0 ≤ norm x := by
  rw [norm]
  linarith [sq_nonneg x.re, sq_nonneg x.im]

theorem norm_pos (x : GaussInt) : 0 < norm x ↔ x ≠ 0 := by
  constructor
  · intro h rfl
    simp [norm] at h
  · intro h
    by_contra!
    by_cases heq : x.norm = 0
    · rw [norm, sq_add_sq_eq_zero] at heq
      apply h; ext <;> tauto
    · have := lt_of_le_of_ne this heq
      rw [norm] at *
      linarith [sq_nonneg x.re, sq_nonneg x.im]

theorem norm_mul (x y : GaussInt) : norm (x * y) = norm x * norm y := by
  simp [norm]; ring

def conj (x : GaussInt) : GaussInt := ⟨ x.re, -x.im ⟩

@[simp]
theorem conj_re (x : GaussInt) : (conj x).re = x.re := rfl
@[simp]
theorem conj_im (x : GaussInt) : (conj x).im = -x.im := rfl

theorem norm_conj (x : GaussInt) : norm (conj x) = norm x := by simp [norm]

#eval Int.ediv 5 2

instance : Div GaussInt :=
  ⟨ fun x y => ⟨ Int.ediv (x * conj y).re (norm y), Int.ediv (x * conj y).im (norm y) ⟩ ⟩
instance : Mod GaussInt :=
  ⟨ fun x y => x - y * (x / y) ⟩ 

theorem div_def (x y : GaussInt) :
    x / y = ⟨ Int.ediv (x * conj y).re (norm y), Int.ediv (x * conj y).im (norm y) ⟩ :=
  rfl

theorem mod_def (x y : GaussInt) : x % y = x - y * (x / y) := rfl

theorem norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have H1 : x % y * conj y = ⟨ Int.emod  (x * conj y).re (norm y), Int.emod (x * conj y).im (norm y) ⟩
  /- · ext <;> simp [Int.emod_eq_iff, mod_def, div_def, norm] <;> ring -/
  sorry
  sorry

end GaussInt
end GaussianIntegers
end M7Structures

