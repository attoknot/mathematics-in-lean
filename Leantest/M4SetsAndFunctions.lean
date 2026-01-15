import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace M4SetsAndFunctions

section Sets

variable {a : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨ xs, xu ⟩
  exact ⟨h _ xs, xu ⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨ xs, xu ⟩
  exact ⟨ h _ xs, xu ⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨ h xsu.1, xsu.2 ⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨ xs, xt | xu ⟩
  · left; exact ⟨ xs, xt ⟩
  · right; exact ⟨ xs, xu ⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨ xs, xt ⟩ | ⟨ xs, xu ⟩)
  · constructor; assumption; left; assumption
  · constructor; assumption; right; assumption
  
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨ xs, xtu ⟩
  constructor; constructor
  · exact xs
  · intro xt
    apply xtu
    left
    exact xt
  · intro xu
    apply xtu
    right
    exact xu

example : s ∩ t = t ∩ s := by
  ext x
  constructor <;> rintro ⟨ ⟩ <;> constructor <;> assumption

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨ xs, xt ⟩; exact ⟨ xt, xs ⟩
  · rintro x ⟨ xt, xs ⟩; exact ⟨ xs, xt ⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun x ⟨ xs, xt ⟩ => ⟨ xt, xs ⟩) (fun x ⟨ xt, xs ⟩ => ⟨ xs, xt ⟩)

example : s ∩ (s ∪ t) = s := by
  ext x; constructor
  · rintro ⟨ xs, xst ⟩; exact xs
  · intro xs; constructor
    · exact xs
    · left; exact xs

example : s ∪ s ∩ t = s := by
  ext x; constructor
  · show x ∈ s ∪ s ∩ t → x ∈ s
    rintro (_ | ⟨ _, _ ⟩) <;> assumption
  · show x ∈ s → x ∈ s ∪ s ∩ t
    intro; left; assumption

example : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨ xs, xnt ⟩ | xt)
    · left; exact xs
    · right; exact xt
  · rintro (xs | xt)
    · by_cases xt : (x ∈ t)
      · right; exact xt
      · left; exact ⟨ xs, xt ⟩
    right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨ xs, xnt ⟩ | ⟨ xt, xns ⟩)
    · constructor
      · left; exact xs
      · rintro ⟨ ⟩; contradiction
    · constructor
      · right; exact xt
      · rintro ⟨ ⟩; contradiction
  · rintro ⟨ xs | xt, xnst ⟩
    · left; constructor
      · exact xs
      · intro xnt; apply xnst; exact ⟨ xs, xnt ⟩
    · right; constructor
      · exact xt
      · intro xns; apply xnst; exact ⟨ xns, xt ⟩

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; by_cases (x ∈ s) <;> by_cases (x ∈ t)
    <;> simp at * <;> tauto

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n ⟨ nprime, ngt ⟩
  simp at nprime ngt ⊢
  rcases Nat.Prime.eq_two_or_odd nprime with h | h
  · linarith
  · apply Nat.odd_iff.mpr h

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs; constructor
  · apply h₀ _ xs
  · apply h₁ _ xs


example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

variable (ssubt : s ⊆ t)
example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs; constructor
  · apply h₀
    apply mem_of_subset_of_mem ssubt xs
  · apply h₁
    apply mem_of_subset_of_mem ssubt xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨ x, xs, ⟨ _, xprime ⟩ ⟩
  use x; constructor
  · apply mem_of_subset_of_mem ssubt xs
  exact xprime

end Sets

section Sets
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)
open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  tauto

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h; constructor
    · intro i; exact (h i).1
    · intro i; exact (h i).2
  · intro h i; constructor
    · exact h.1 i
    · exact h.2 i

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · rintro (xs | xa)
    · intro i; right; exact xs
    · intro i; simp only [mem_iInter] at xa;  
      left; apply xa
  · by_cases xs : (x ∈ s)
    · intro; left; exact xs
    · intro xa; right; simp only [mem_iInter]
      intro i; rcases xa i <;> tauto

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  simp only [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  ext x
  simp
  rcases Nat.exists_infinite_primes x with ⟨ i, ⟨ ige, iprime ⟩ ⟩
  use i; constructor
  · simp [primes]
    exact iprime
  · exact ige

end Sets

section Functions

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : s ⊆ f⁻¹' (f '' s) := by
  intro x xs
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  simp only [image, preimage]
  constructor
  · show {x | ∃ a ∈ s, f a = x} ⊆ v → s ⊆ {x | f x ∈ v}
    intro fssub x xs
    dsimp; show f x ∈ v
    apply @fssub (f x)
    use x, xs
  · show s ⊆ {x | f x ∈ v} → {x | ∃ a ∈ s, f a = x} ⊆ v
    intro subfv x xs
    dsimp at xs; rcases xs with ⟨ a, as, rfl ⟩
    apply subfv as
    
/- Injective     ∀ a1 a2, f a1 = f a2 → a1 = a2 -/
/- Surjective    ∀ b, ∃ a, f a = b -/
/- image      '' (f : α → β) (s : Set α) : Set β -/
/- preimage  ⁻¹' (f : α → β) (s : Set β) : Set α -/


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  simp only [Injective, image, preimage] at *
  intro x xs
  dsimp at xs; rcases xs with ⟨ a, as, fa ⟩
  rw [←h fa]
  exact as

example : f '' (f ⁻¹' u) ⊆ u := by
  simp only [image, preimage]
  intro x ⟨ y, ⟨ fy, eq ⟩ ⟩
  rw [←eq]
  dsimp at fy
  apply fy

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  simp only [Surjective, image, preimage] at *
  intro x xu
  rcases (h x) with ⟨ a, rfl ⟩
  use a
  exact ⟨ xu, rfl ⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro x ⟨ a, as, fa ⟩
  use a
  constructor
  · apply mem_of_subset_of_mem h as
  · exact fa

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  grind

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry  


variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp; constructor
  · show (∃ x, (∃ i, x ∈ A i) ∧ f x = y) → ∃ i, ∃ x ∈ A i, f x = y
    rintro ⟨ x, ⟨ i, xai ⟩, fxeqy ⟩
    use i, x, xai, fxeqy
  · show (∃ i, ∃ x ∈ A i, f x = y) → ∃ x, (∃ i, x ∈ A i) ∧ f x = y
    rintro ⟨ i, x, xai, fxeqy ⟩
    use x, ⟨ i, xai ⟩, fxeqy

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry   

open Set Real

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x hx y hy
  apply (sqrt_inj hx hy).mp

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x hx y hy
  apply Iff.mp
  calc x ^ 2 = y ^ 2
    _ ↔ √(x^2) = √(y^2) := by symm; apply sqrt_inj <;> apply sq_nonneg
    _ ↔ x = y := by rw [sqrt_sq hx, sqrt_sq hy]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x; constructor
  · intro ⟨ a, ha, aeq ⟩
    rw [←aeq]
    apply sqrt_nonneg
  · intro hx
    use (x^2); constructor
    · change x^2 ≥ 0; apply sq_nonneg
    · apply sqrt_sq hx

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x; constructor
  · intro hx;
    simp at hx; rcases hx with ⟨ y, rfl ⟩
    dsimp; apply sq_nonneg
  · intro hx
    simp; use √x
    apply sq_sqrt hx

end Functions

noncomputable section Inverse

variable {α β : Type*} [Inhabited α]
variable (P : α → Prop) (h : ∃ x, P x)

example : P (Classical.choose h) :=
  Classical.choose_spec h

open Classical

def inverse (f : α → β) : β → α := fun y : β =>
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β}  (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  apply choose_spec h

variable (f : α → β)
open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  rw [Injective, LeftInverse]; constructor
  · intro inj x
    apply inj
    apply inverse_spec
    use x
  · intro inv x y eq
    rw [←inv x, ←inv y]
    congr

example : Injective f ↔ LeftInverse (inverse f) f := by
  rw [Injective, LeftInverse]; constructor
  · intro inj x; apply inj (inverse_spec _ ⟨x, rfl⟩)
  · intro inv x y eq; rw [←inv x, ←inv y, ←eq]  
  
example : Surjective f ↔ RightInverse (inverse f) f := by
  rw [Surjective, RightInverse, LeftInverse]; constructor
  · intro surj x
    apply inverse_spec
    apply surj
  · intro inv y
    use (inverse f y)
    apply inv

end Inverse

theorem Cantor : ∀ f : α → Set α, ¬Function.Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  · dsimp only [S]
    exact h₁
    
  have h₃ : j ∉ S
  · intro hj
    apply h₁
    rw [←h] at hj
    exact hj
  contradiction

noncomputable section ShroderBernstein

variable {α β : Type*} [Nonempty β]
open Classical Function Set

#check invFun
#check invFun_eq

variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet := ⋃ n, sbAux f g n

def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
    exact ⟨ trivial, hx ⟩
  have : ∃ y, g y = x := by
    rcases this with ⟨ a, _, eq ⟩
    use a, eq
  rw [invFun_eq this]

theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂ heq
  simp only [h_def] at heq
  by_cases xina : x₁ ∈ A ∨ x₂ ∈ A
  · wlog hx₁ : x₁ ∈ A generalizing x₁ x₂ heq xina
    · symm
      apply this <;> try symm; assumption
      rcases xina <;> trivial
    have hx₂ : x₂ ∈ A := by
      apply _root_.not_imp_self.mp
      intro (hnx₂ : x₂ ∉ A)
      have x₂eq : x₂ = g (f x₁) := by
        rw [(_   : f x₁ = sbFun f g x₁)]
        rw [(heq : sbFun f g x₁ = sbFun f g x₂)]
        · show x₂ = g (sbFun f g x₂)
          rw [sbFun, if_neg hnx₂]
          symm
          apply sb_right_inv f g hnx₂
        · rw [sbFun, if_pos hx₁]
      rw [sbFun, sbFun, if_pos hx₁, if_neg hnx₂] at heq
      rw [A_def, sbSet, mem_iUnion] at hx₁
      rw [A_def, sbSet, mem_iUnion]
      rcases hx₁ with ⟨ n, hn ⟩
      use n + 1
      simp [sbAux]
      exact ⟨ x₁, hn, x₂eq.symm ⟩
    simp [sbFun] at heq
    rw [if_pos hx₁, if_pos hx₂] at heq
    apply hf heq

  · push_neg at xina
    rw [sbFun, sbFun, if_neg xina.1, if_neg xina.2] at heq
    rw [←sb_right_inv _ _ xina.1, ←sb_right_inv _ _ xina.2]
    congr

theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    rw [h_def, sbFun, if_pos this]
    apply hg hx

  · use g y
    rw [h_def, sbFun, if_neg gyA]
    apply hg
    apply sb_right_inv f g gyA

theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩

end ShroderBernstein
end M4SetsAndFunctions
