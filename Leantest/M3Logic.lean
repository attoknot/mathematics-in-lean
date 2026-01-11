import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem my_lemma : ∀ {x y ε : ℚ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intros x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by apply mul_le_mul_of_nonneg <;> (try apply abs_nonneg) <;> linarith
    _ < 1 * ε := by apply (mul_lt_mul_iff_of_pos_right _).mpr <;> linarith
    _ = ε := by linarith

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a


example {f g a b} (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x => f x + g x) (a + b) := by
  intro x
  change f x + g x ≤ a + b
  apply add_le_add
  apply hfa
  apply hgb

example {f g a b} (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  change a + b ≤ f x + g x
  apply add_le_add
  apply hfa
  apply hgb

example {f g} (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  change 0 ≤ f x * g x
  apply mul_nonneg
  apply nnf
  apply nng

example {f g a b} (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x => f x * g x) (a * b) := by
  intro x
  dsimp
  apply mul_le_mul
  · apply hfa
  · apply hgb
  · apply nng
  · apply nna

example {c : ℝ} {f : ℝ → ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intros a b aleb
  apply mul_le_mul_of_nonneg_left
  · apply mf aleb
  · apply nnc

example {c : ℝ} {f : ℝ → ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb => mul_le_mul_of_nonneg_left (mf aleb) nnc

example (f g : ℝ → ℝ) (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intros a b aleb
  apply mf
  apply mg
  apply aleb

example (f g : ℝ → ℝ) (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb => mf (mg aleb)

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example {f g} (ef : FnEven f) (eg : FnEven g) : FnEven fun x => f x + g x := by
  intro x
  change f x + g x = _
  rw [ef, eg]

example {f g} (of : FnOdd f) (og : FnOdd g) : FnEven fun x => f x * g x := by
  intro x
  calc f x * g x
    _ = -f (-x) * -g (-x) := by rw [of, og]
    _ = f (-x) * g (-x) := by rw [neg_mul_neg]

example {f g} (ef : FnEven f) (og : FnOdd g) : FnOdd fun x => f x * g x := by
  intro x
  calc f x * g x
    _ = f (-x) * -g (-x) := by rw [ef, og]
    _ = -(f (-x) * g (-x)) := by rw [mul_neg]

example {f g} (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  change f (g x) = f (g (-x))
  rw [ef, og, neg_neg]

namespace Sets

variable {α : Type*} [PartialOrder α]

example (r s t : Set α) : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rsubs ssubt  x xinr
  apply ssubt
  apply rsubs
  apply xinr

def SetUb (s : Set α) (a : α) :=
  ∀ x : α, x ∈ s → x ≤ a

example (s : Set α) (a b : α) (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xins
  apply h at xins
  trans a <;> assumption

open Function

example (c : ℝ) : Injective fun x => x + c := by
  intro x₁ x₂ h'
  dsimp at h'
  apply (add_left_inj c).mp
  assumption

example {c : ℝ} (h : c ≠ 0) : Injective fun x => c * x := by
  intros x₁ x₂ h'
  dsimp at h'
  apply (mul_right_inj' h).mp
  assumption

end Sets

namespace ExistentialQuantifier

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5/2
  constructor <;> linarith

example {f g : ℝ → ℝ} (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x => f x + g x := by
  rcases lbf with ⟨ a ⟩
  rcases lbg with ⟨ b ⟩
  use a + b
  intro x
  apply add_le_add <;> apply_assumption

example {f : ℝ → ℝ} {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨ a ⟩
  use c * a
  intro x
  apply mul_le_mul_of_nonneg_left <;> apply_assumption

variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2
  
theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨ xa, xb, rfl ⟩
  rcases sosy with ⟨ ya, yb, rfl ⟩
  use xa * ya - xb * yb, xa * yb + xb * ya
  ring

example (a b c : ℚ) (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨ n, rfl ⟩
  rcases divac with ⟨ m, rfl ⟩
  use n + m
  rw [mul_add]

open Function

example {c : ℝ} : Surjective fun x => x + c := by
  intro x
  use x - c
  dsimp; ring

example {c : ℝ} (h : c ≠ 0) : Surjective fun x => c * x := by
  intro x
  use x / c
  dsimp; rw [mul_div_cancel₀ _ h]

example {x y : ℝ} (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro x
  rcases surjg x with ⟨ xg, hxg ⟩
  rcases surjf xg with ⟨ xf, hxf ⟩
  use xf
  change g (f xf) = x
  rw [hxf, hxg]

end ExistentialQuantifier

namespace Negation

example {a b : ℕ} (h : a < b) : ¬b < a := by
  intro h'
  apply lt_irrefl a
  trans b <;> assumption

example {f} (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  rintro ⟨ a, albf ⟩
  rcases h a with ⟨ x, hx ⟩
  apply lt_irrefl (f x)
  apply lt_of_lt_of_le hx
  apply albf

example : ¬FnHasUb fun x => x := by
  rintro ⟨ a, alb ⟩
  have h : a + 1 ≤ a := alb (a + 1)
  apply lt_irrefl (a+1)
  apply lt_of_le_of_lt h
  linarith

example : ¬FnHasUb fun x => x := by
  rintro ⟨ a, alb ⟩
  linarith [alb (a+1)]

example {f : ℝ → ℝ} (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intros blea
  linarith [h blea] /- i can't resist the urge to use linarith -/

example {f : ℝ → ℝ} (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intros mf
  apply not_le_of_gt h' (mf h)

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f : ℝ → ℝ := fun x => 0
  have monof : Monotone f := fun _ _ _ => by rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith

variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intros x hx
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨ x, hx ⟩
  apply h x hx

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  apply h'
  use x

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨ x, hx ⟩
  apply hx
  apply h'

example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h
  apply h'

example (h : Q) : ¬¬Q := by
  intros h'
  apply h'
  apply h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intros a
  by_contra h'
  apply h
  use a
  intros x
  apply le_of_not_gt
  intros hgt
  apply h'
  use x

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  /- T_T -/
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example {f : ℝ → ℝ} (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  assumption

end Negation

namespace ConjunctionAndIff

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]

variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_ge]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> try assumption
  · rintro eq
    rw [eq] at h1 h2
    exact h2 h1
  · intro blea
    apply h2
    apply le_antisymm <;> assumption

end ConjunctionAndIff

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  cases le_or_gt 0 x
  next h =>
    rw [abs_of_nonneg]
    assumption
  next h =>
    rw [abs_of_neg] <;> linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  cases le_or_gt 0 x
  next h =>
    rw [abs_of_nonneg] <;> linarith
  next h =>
    rw [abs_of_neg]; assumption

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 x with hx | hx
    <;> rcases le_or_gt 0 y with hy | hy
    <;> rcases le_or_gt 0 (x + y) with hxy | hxy
    <;> (try rw [abs_of_nonneg hx]) <;> (try rw [abs_of_neg hx])
    <;> (try rw [abs_of_nonneg hy]) <;> (try rw [abs_of_neg hy])
    <;> (try rw [abs_of_nonneg hxy]) <;> (try rw [abs_of_neg hxy])
    <;> try linarith

theorem lt_abs (x y : ℝ) : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
    <;> (try rw [abs_of_nonneg h])
    <;> (try rw [abs_of_neg h])
    <;> constructor
    <;> (try rintro (h2 | h2); linarith)
    <;> (try linarith)
  · intro _; left; assumption
  · intro _; right; assumption

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
    <;> (try rw [abs_of_nonneg h]) <;> (try rw [abs_of_neg h])
    <;> constructor
    <;> (try intro _; constructor)
    <;> (try rintro ⟨_, _⟩)
    <;> linarith

end MyAbs

section MoreDisjunctions

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h : x ^ 2 - 1 ^ 2 = 0 := by rw [h]; ring
  have h : (x + 1) * (x - 1) = 0 := by ring_nf at *; assumption
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with h | h
  · right; linarith
  · left; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h : x ^ 2 - y ^ 2 = 0 := by rw [h]; ring
  have h : (x + y) * (x - y) = 0 := by ring_nf at *; assumption
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with h | h
  · right; linarith
  · left; linarith

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor <;> rcases em P
  · intro f; right; apply f; assumption
  · intro _; left; assumption
  all_goals rintro (_ | _)
    <;> try intro; exfalso; apply_assumption; assumption
  · intro; assumption

end MoreDisjunctions

section Sequences

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro _ _
  change |a - a| < ε
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n nge
  have hs := hs n (le_trans (le_max_left _ _) nge)
  have ht := ht n (le_trans (le_max_right _ _) nge)
  /- rw [(by ring : ε = ε / 2 + ε / 2)]
   - rw [(by ring : s n + t n - (a + b) = s n - a + (t n - b))] -/
  rcases le_or_gt 0 (s n - a) with hs | hs
    <;> rcases le_or_gt 0 (t n - b) with ht | ht
    <;> rcases le_or_gt 0 ( s n + t n - (a + b)) with hst | hst
    <;> (try (rw [abs_of_nonneg hs] at *)) <;> (try (rw [abs_of_neg hs] at *))
    <;> (try (rw [abs_of_nonneg ht] at *)) <;> (try (rw [abs_of_neg ht] at *))
    <;> (try (rw [abs_of_nonneg hst])) <;> (try (rw [abs_of_neg hst]))
    <;> linarith

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]; ring
    rw [h]; ring
  have acpos : 0 < |c| := abs_pos.mpr h
  change ∀ ε > 0, ∃ N, ∀ n ≥ N, |c * s n - c * a| < ε
  intro ε εpos
  rcases cs (ε / |c|) (by field_simp; linarith) with ⟨Ns, hs⟩
  use Ns
  intro n nge
  specialize hs n nge
  field_simp at hs
  rw [←abs_mul, mul_comm, mul_sub] at hs
  assumption

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n ≥ N, |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intros n nge
  specialize h n nge
  rw [add_comm _ 1]
  apply lt_add_of_sub_right_lt
  apply lt_of_le_of_lt _ h
  apply abs_sub_abs_le_abs_sub

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  rcases cs _ pos₀ with ⟨N₂, h₂⟩ 
  use (max N₀ (max N₁ N₂))
  intros n nge
  specialize h₀ n (by grind)
  specialize h₁ n (by grind)
  specialize h₂ n (by grind)
  field_simp at h₁
  field_simp at h₂
  rw [(by ring : t n - 0 = t n)] at *
  calc |s n * t n - 0|
    _ = |s n| * |t n| := by ring_nf; rw [←abs_mul]
    _ ≤ B * |t n| := by apply mul_le_mul <;> linarith [abs_nonneg (t n)]
    _ < ε := by rw [mul_comm]; assumption

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
    (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n => s n * t n) (a * b) := by
  have ci : ConvergesTo (fun n => s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  convert convergesTo_add ci (convergesTo_mul_const b cs) using 1
  · funext; ring
  ring
  
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  let ε := |a - b| / 2
  have εpos : 0 < ε := by apply half_pos; rw [abs_pos, sub_ne_zero]; exact abne
  rcases sa ε εpos with ⟨Na, ha⟩
  rcases sb ε εpos with ⟨Nb, hb⟩
  let N := max Na Nb
  specialize ha N (by grind)
  specialize hb N (by grind)
  dsimp only [ε] at *
  have tr : |a - b| ≤ |a - s N| + |s N - b| := dist_triangle a (s N) b
  rw [abs_sub_comm a (s N)] at tr
  linarith
