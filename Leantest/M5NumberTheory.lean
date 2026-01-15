import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic

namespace M5NumberTheory

open Nat

section IrrationalRoots

#check Prime.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
    apply even_of_even_sqr
    /- apply dvd_iff_exists_eq_mul_left.mpr -/
    use n^2
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' (by trivial)).mp this   
  have : 2 ∣ n := by
    apply even_of_even_sqr
    use k^2
    linarith
  have : 2 ∣ m.gcd n := by
    apply Nat.dvd_gcd <;> assumption
  have : 2 ∣ 1 := by
    rw [coprime_mn] at this
    apply this
  norm_num at this
  
theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    /- simpa -/
    rw [factorization_pow']
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [factorization_mul', factorization_pow', Nat.Prime.factorization' prime_p]; linarith [eq1]
    · linarith [Prime.two_le prime_p]
    · assumption
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  by_cases rnz : r = 0
  · simp [rnz]
  have npow_nez : n ^ k ≠ 0 := by apply pow_ne_zero; assumption
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by simp
  have eq2 : (r * n ^ k).factorization p = k * n.factorization p + r.factorization p := by
    rw [factorization_mul' rnz npow_nez, factorization_pow', add_comm]
  have : r.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  apply Nat.dvd_sub <;> apply dvd_mul_right

end IrrationalRoots

section Induction

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]; linarith
  rw [fac]
  exact mul_pos n.succ_pos ih

theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exfalso; linarith
  rw [fac]
  by_cases ieq : i = n+1
  · rw [ieq]
    apply dvd_mul_right
  apply dvd_mul_of_dvd_right
  apply ih
  apply le_of_lt_succ
  apply lt_of_le_of_ne ile ieq

theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  induction' n with n ih
  · simp [fac]
  rw [Nat.add_one_sub_one, pow_succ, fac, mul_comm _ 2]
  rw [Nat.add_one_sub_one] at ih
  apply Nat.mul_le_mul _ ih
  linarith

variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

open BigOperators
open Finset

example : s.sum f = ∑ x ∈ s, f x := rfl

example (n : ℕ) : fac n = ∏ i ∈ range n, (i + 1) := by
  induction' n with n hn
  · dsimp [fac]
  rw [fac, hn, Finset.prod_range_succ]
  linarith

theorem sum_id (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right
  · linarith
  induction' n with n hn
  · rw [Finset.sum_range_succ]; dsimp
  rw [Finset.sum_range_succ, mul_add 2, ←hn]; 
  linarith

theorem sum_sqr (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm; apply Nat.div_eq_of_eq_mul_right
  · linarith
  induction' n with n hn
  · rw [Finset.sum_range_succ]; dsimp
  rw [Finset.sum_range_succ, mul_add 6, ←hn]
  linarith

end Induction

section InfinitePrimes

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  rcases m with _ | m; contradiction
  rcases m with _ | m; contradiction
  linarith
  
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_cases (2 ≤ m); assumption
  interval_cases m <;> contradiction

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, Nat.Prime p ∧ p ∣ n := by
  by_cases primen : Nat.Prime n
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [not_prime_iff_exists_dvd_ne h] at primen
  rcases primen with ⟨ m, ⟨ mdvdn, mne1, mnen ⟩ ⟩
  by_cases primem : Nat.Prime m
  · use m
  have mne0 : m ≠ 0 := by rintro rfl; rw [Nat.zero_dvd] at mdvdn; linarith
  have mge2 : 2 ≤ m := two_le mne0 mne1
  have mltn : m < n := by
    apply lt_of_le_of_ne _ mnen
    apply Nat.le_of_dvd _ mdvdn
    linarith
  rcases ih m mltn mge2 primem with ⟨ p, hp ⟩
  use p
  exact ⟨ hp.1, dvd_trans hp.2 mdvdn ⟩

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  let k := Nat.factorial n + 1
  rcases n with _ | n; use 2; constructor; linarith; exact prime_two
  rcases n with _ | n; use 2; constructor; linarith; exact prime_two
  have kge2 : 2 ≤ k := by
    simp [k, Nat.factorial]
    ring_nf
    apply Nat.lt_add_left
    simp
    apply factorial_pos
  rcases exists_prime_factor kge2 with ⟨ p, ⟨ hp, pdvdk ⟩ ⟩
  use p; symm; constructor; exact hp
  by_contra! h
  dsimp only [k] at pdvdk
  have := Nat.dvd_factorial (Prime.pos hp) h
  have : p ∣ 1 := by
    convert dvd_sub pdvdk this
    rw [add_sub_self_left]
  apply Nat.Prime.not_dvd_one hp this

variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext; simp; tauto
example : (r \ s) \ t = r \ (s ∪ t) := by
  ext; simp; tauto

open Finset

theorem eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  rcases Prime.eq_one_or_self_of_dvd prime_q _ h with rfl | rfl
  · exfalso
    apply Nat.not_prime_one prime_p
  · rfl

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · dsimp at h₁
    exfalso
    apply Nat.Prime.not_dvd_one prime_p h₁
  simp at ⊢ h₀
  rw [prod_insert ans, Nat.dvd_mul] at h₁
  rcases h₁ with ⟨ k₁, k₂, k₁dvda, k₂dvds, peq ⟩
  cases (Nat.dvd_prime h₀.1).mp k₁dvda
  case inl k₁eq1 =>
    right
    apply ih h₀.2
    show p ∣ ∏ n ∈ s, n
    rw [k₁eq1, one_mul] at peq
    rw [peq] at k₂dvds
    exact k₂dvds
  case inr k₁eqa =>
    rw [k₁eqa] at peq
    by_cases! k₂eq1 : k₂ ≠ 1
    · rw [←peq] at prime_p
      exfalso; apply Nat.not_prime_mul _ k₂eq1 prime_p
      apply h₀.1.ne_one
    rw [k₂eq1, mul_one] at peq
    rw [←peq]
    left; rfl

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra! h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
    simp; change 0 < _
    apply Finset.prod_pos
    intro i is'
    rw [s'_def, mem_filter] at is'
    apply Nat.Prime.pos is'.2
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
    apply Finset.dvd_prod_of_mem
    rw [s'_def, mem_filter]
    exact ⟨ h _ pp, pp ⟩
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  show False
  apply Nat.Prime.not_dvd_one pp this

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases m % 4 <;> simp
  rw [←Nat.mul_mod_mod]
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  · apply Nat.div_dvd_of_dvd h₀
  · apply Nat.div_lt_self <;> linarith

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  . by_cases primem : m.Prime
    · use m
    rcases ih m mltn h1 primem with ⟨ mm, primemm, mmdvdm, hmm ⟩
    use mm, primemm, dvd_trans mmdvdm mdvdn, hmm
  · have mdvdn : n / m ∣ n := by use m; nth_rw 1 [←neq]; ring
    have mltn : n / m < n := by apply Nat.div_lt_self <;> linarith
    by_cases primem : (n / m).Prime
    · use (n / m)
    rcases ih (n / m) mltn h1 primem with ⟨ mm, primemm, mmdvdm, hmm ⟩
    use mm, primemm, dvd_trans mmdvdm mdvdn

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨ s, hs ⟩
  use s.sup id + 1
  intro k qk
  apply lt_succ_of_le
  show k ≤ s.sup id
  apply Finset.le_sup (hs k qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨ n, hn ⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  apply hn k
 
theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i ∈ erase s 3, i) + 3) % 4 = 3 := by
    rw [add_comm _ 3, Nat.add_mul_mod_self_left]
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    apply (hs p).mp
    exact ⟨ pp, p4eq ⟩
  have pne3 : p ≠ 3 := by
    rintro peq
    have := Nat.dvd_sub pdvd (by rw [peq] : p ∣ 3)
    rw [add_sub_self_right, Coprime.dvd_mul_left (by rw [peq]; norm_num)] at this
    have sp : ∀ n ∈ s.erase 3, n.Prime := by
      intro n hn
      rw [mem_erase] at hn
      exact ((hs n).mpr hn.2).1
    have pmem : p ∈ s.erase 3 := mem_of_dvd_prod_primes pp sp this
    rw [mem_erase] at pmem
    apply pmem.1 peq
  have : p ∣ 4 * ∏ i ∈ s.erase 3, i := by
    apply dvd_trans
    · show p ∣ ∏ i ∈ s.erase 3, i
      apply dvd_prod_of_mem
      rw [mem_erase]
      exact ⟨ pne3, ps ⟩
    · apply dvd_mul_left
  have : p ∣ 3 := by
    convert dvd_sub pdvd this
    rw [add_sub_self_left]
  have : p = 3 := by
    rw [←Nat.prime_dvd_prime_iff_eq pp prime_three]
    exact this
  contradiction

end InfinitePrimes

namespace MoreInduction

@[simp] def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl

example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by rw [fib]

noncomputable section

open Real

def phi  : ℝ := (1 + √5) / 2
def phi' : ℝ := (1 - √5) / 2

theorem phi_sq : phi^2 = phi + 1 := by
  rw [phi]
  ring_nf
  rw [sq_sqrt]
  · ring
  · norm_num

theorem phi'_sq : phi'^2 = phi' + 1 := by
  rw [phi']
  ring_nf
  rw [sq_sqrt]
  · ring
  · norm_num

theorem fib_eq : ∀ n, fib n = (phi^n - phi'^n) / √5
  | 0 => by simp
  | 1 => by simp [phi, phi']; field_simp; ring
  | n + 2 => by
    simp [fib_eq]
    field_simp
    simp only [pow_add, phi_sq, phi'_sq]
    ring

theorem fib_coprime_fib_succ (n : ℕ) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [fib]
    rw [Nat.coprime_add_self_right]
    apply Coprime.symm ih

def fib' (n : ℕ) : ℕ :=
  aux n 0 1
where aux
  | 0,   x, _ => x
  | n+1, a, b => aux n b (a + b)

theorem fib'.aux_eq (m n : ℕ) : fib'.aux n (fib m) (fib (m + 1)) = fib (n + m) := by
  revert m
  induction' n with n ih
  · simp [aux]
  intro m
  rw [aux]
  have : fib m + fib (m + 1) = fib (m + 2) := by simp
  rw [this, ih (m + 1)]
  congr 1
  ring

theorem fib'_eq_fib (n : ℕ) : fib n = fib' n := by
  rw [fib']
  have := fib'.aux_eq 0 n
  simp at this
  symm; exact this

end
end MoreInduction
end M5NumberTheory
