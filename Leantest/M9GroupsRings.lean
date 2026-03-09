import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.GroupTheory.Sylow
import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

namespace M9GroupsRings


example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x
example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
  (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
  f.map_mul x y

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
  f.map_inv x

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
    G →* H :=
  MonoidHom.mk' f h

noncomputable example {G H : Type*} [Group G] [Group H]
    (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h

example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    x * y ∈ H :=
  H.mul_mem hx hy

example {G : Type*} [Group G] (H H' : Subgroup G) :
  ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]

example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial
example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1, H.one_mem
    group
  inv_mem' := by
    dsimp
    intro a ⟨ b, hb, hab ⟩ 
    use b⁻¹, H.inv_mem hb
    rw [hab]
    group
  mul_mem' := by
    dsimp
    rintro a b ⟨ c, hc, hac ⟩ ⟨ d, hd, hbd ⟩
    use c * d, H.mul_mem hc hd
    rw [hac, hbd]
    group

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  intro x
  simp only [mem_comap]
  apply hST

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  intro x
  simp only [mem_map]
  intro ⟨ a, ha, hax ⟩
  use a, hST ha

variable {K : Type*} [Group K]

example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  ext x; constructor
  iterate 2
    simp only [mem_comap]
    dsimp
    exact id

example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  ext x; constructor
  · simp only [mem_map]
    dsimp
    rintro ⟨ a, ha, hxa ⟩
    rw [←hxa]
    use (φ a); constructor
    · use a
    · rfl
  · simp only [mem_map]
    dsimp
    rintro ⟨ a, ⟨ b, _, _ ⟩, _ ⟩
    use b; grind
end exercises

section
open scoped Classical

example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
  ⟨ G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm ⟩

open Subgroup

example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd

open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
  Perm.closure_isCycle

#simp [mul_assoc] (c[1, 2, 3] : Perm (Fin 5)) * c[2, 3, 4]

section FreeGroup

inductive S | a | b | c
open S

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹

def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]


def myGroup := PresentedGroup {.of () ^ 3} deriving Group

def myMap : Unit → Perm (Fin 5)
| () => c[1, 2, 3]

lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp
  decide

end FreeGroup
end

noncomputable section GroupActions
open MulAction

example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
    g • (g' • x) = (g * g') • x :=
  (mul_smul g g' x).symm

def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
  Equiv.Perm.subgroupOfMulAction G G

example {G X : Type*} [Group G] [MulAction G X] : Setoid X := orbitRel G X

example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out ω)) :=
  MulAction.selfEquivSigmaOrbits G X

#check Fintype.card_congr

example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

-- G = S3
-- X = Z
-- group action: permute the last 3 bits
-- the action is "injective"
-- orbit of   0 is {0}
-- orbit of   1 is {001,010,100}
-- orbit of  11 is {011,101,110}
-- orbit of 111 is {111}
-- orbit of 1000 is the same as 0
-- stabilizer of 000 is G
-- stabilizer of 001 is {(),(23)}
-- stabilizer of 011 is {(12)}
-- stabilizer of 111 is G

variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  ext x; constructor
  · change (∃ h ∈ H, x = 1 * h * 1⁻¹) → x ∈ H
    rintro ⟨ h, ⟨ hh, rfl ⟩ ⟩
    group
    exact hh
  · simp [conjugate]

instance : SMul G (Subgroup G) where
  smul := conjugate
instance : MulAction G (Subgroup G) where
  one_smul := by
    intros H
    show conjugate 1 H = H
    rw [conjugate_one]
  mul_smul := by
    intros x y H
    show conjugate (x * y) H = conjugate x (conjugate y H)
    simp [conjugate]
    group
end GroupActions

noncomputable section QuotienGroups

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
  QuotientGroup.mk' H

example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
    [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
  QuotientGroup.lift N φ h

example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ φ.ker →* φ.range :=
  QuotientGroup.quotientKerEquivRange φ

section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
  rw [←Subgroup.index_eq_card]
  rw [←Subgroup.index_mul_card H, mul_comm] at h'
  apply Nat.eq_of_mul_eq_mul_left _ h'
  apply Nat.card_pos

variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

def iso₁ : K ≃* G ⧸ H := by
  sorry

def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
  sorry

#check MulEquiv.prodCongr

def finalIso : G ≃* H × K :=
  sorry

end
end QuotienGroups

section Rings

example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

-- TODO:
-- i don't know anything about ring theory

end Rings

end M9GroupsRings

