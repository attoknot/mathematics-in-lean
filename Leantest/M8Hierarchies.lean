import Mathlib.Tactic

namespace M8Hierarchies

class One₁ (α : Type) where
  /-- the element one -/
  one : α
@[class] structure One₂ (α : Type) where
  one : α
#check One₁.one
#check One₂.one

@[inherit_doc]
notation "𝟙" => One₁.one


class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ " => Dia₁.dia

class Semigroup₀ (α : Type) where
  to_dia₁ : Dia₁ α
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
attribute [instance] Semigroup₀.to_dia₁
example {α : Type} [Semigroup₀ α] (a b : α) : α := a ⋄ b

class Semigroup₁ (α : Type) extends toDia₁ : Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

class Semigroup₂ (α : Type) extends Dia₁ α where
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
class DiaOne₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOne₁ α] (a b : α) : Prop := a ⋄ b = 𝟙

class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOne₁ α
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOne₁ : DiaOne₁ α

#check Monoid₁.mk
#check Monoid₂.mk
#check Monoid₁.toDiaOne₁

class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙
  
lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOne₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOne₁.dia_one b]

export DiaOne₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)

example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]

/- though, i could've copied this from M2Basic.Mygroup -/
lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b := by
  rw [left_inv_eq_right_inv₁ (inv_dia a) h]

class AddSemigroup₃ (α : Type) extends Add α where
  /-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
  /-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0
@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1

attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  rw [left_inv_eq_right_inv' (Group₃.inv_mul a) h]

@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] (a : G) : a * a⁻¹ = 1 := by
  nth_rw 1 [← inv_eq_of_mul (Group₃.inv_mul a)]
  apply Group₃.inv_mul (a⁻¹)

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← one_mul c, ← Group₃.inv_mul a]
  simp only [Semigroup₃.mul_assoc₃]
  congr 1

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
  rw [← mul_one b, ← mul_one c, ← Group₃.mul_inv a]
  simp only [← Semigroup₃.mul_assoc₃]
  congr 1

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ add_comm := by
    intros a b
    have hl : (a + b) * (1 + 1) = a * 1 + b * 1 + a * 1 + b * 1 := by
      rw [Ring₃.left_distrib, Ring₃.right_distrib, ← AddSemigroup₃.add_assoc₃]
    have hr : (a + b) * (1 + 1) = a * 1 + a * 1 + b * 1 + b * 1 := by
      rw [Ring₃.right_distrib, Ring₃.left_distrib, Ring₃.left_distrib, ← AddSemigroup₃.add_assoc₃]
    rw [hl] at hr
    simp [mul_one] at hr
    apply add_right_cancel₃ at hr
    simp only [AddSemigroup₃.add_assoc₃] at hr
    apply add_left_cancel₃ at hr
    exact hr.symm
    }

class LE₁ (α : Type) where
  /-- The less-or-equal relation -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type) extends LE₁ α where
  le_rfl (a : α) : a ≤₁ a
  le_trans (a b c : α) : a ≤₁ b → b ≤₁ c → a ≤₁ c

class PartialOrder₁ (α : Type) extends Preorder₁ α where
  le_antisymm (a b : α) : a ≤₁ b → b ≤₁ a → a = b

/- boring -/

structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'

@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H] where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'  

instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ => G → H) where
  coe := MonoidHom₁.toFun
attribute [coe] MonoidHom₁.toFun

example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 := f.map_one

@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H] where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ => G → H) where
  coe := AddMonoidHom₁.toFun
attribute [coe] MonoidHom₁.toFun

example [AddMonoid G] [AddMonoid H] (f : AddMonoidHom₁ G H) : f 0 = 0 := f.map_zero

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance (M N : Type) [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ => M → N) where
  coe := MonoidHomClass₂.toFun
attribute [coe] MonoidHomClass₂.toFun

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f => f.map_one
  map_mul := fun f => f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f => f.toMonoidHom₁.toFun
  map_one := fun f => f.toMonoidHom₁.map_one
  map_mul := fun f => f.toMonoidHom₁.map_mul

lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m n : M} (h : m * n = 1) :
    f m * f n = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m n : M} (h : m * n = 1) : f m * f n = 1 :=
  map_inv_of_inv f h

class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ => N) where
  map_one : ∀ f : F, f 1  = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' _ _ := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul

@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
    MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β] extends
    DFunLike F α (fun _ => β) where
  le_of_le : ∀ (f : F) a b, a ≤ b → f a ≤ f b

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where
  coe := OrderPresHom.toFun
  coe_injective' _ _ := OrderPresHom.ext
  le_of_le := OrderPresHom.le_of_le

#print OrderPresMonoidHom
instance (α β : Type) [Monoid α] [LE α] [Monoid β] [LE β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
  coe x := (OrderPresMonoidHom.toOrderPresHom x).toFun
  coe_injective' _ _ := OrderPresMonoidHom.ext
  le_of_le x := (OrderPresMonoidHom.toOrderPresHom x).le_of_le

instance (α β : Type) [Monoid α] [LE α] [Monoid β] [LE β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β where
  map_one f := f.map_one
  map_mul f := f.map_mul

@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  carrier : Set M
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier

instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext

example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem
example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N

instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y => ⟨ x * y, N.mul_mem x.property y.property ⟩
  mul_assoc := fun x y z => SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨ 1, N.one_mem ⟩
  one_mul := fun x => SetCoe.ext (one_mul (x : M))
  mul_one := fun x => SetCoe.ext (mul_one (x : M))

class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


@[ext]
structure Subgroup₁ (G : Type) [Group G] where
  carrier : Set G
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem : 1 ∈ carrier
  inv_mem {a}: a ∈ carrier → a⁻¹ ∈ carrier 

instance [Group G] : SetLike (Subgroup₁ G) G where
  coe := Subgroup₁.carrier
  coe_injective' _ _ := Subgroup₁.ext

instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem := Subgroup₁.mul_mem
  one_mem := Subgroup₁.one_mem

instance Subgroup₁Group [Group G] (H : Subgroup₁ G) : Group H where
  mul := fun ⟨ x, hx ⟩ ⟨ y, hy ⟩ => ⟨ x * y, H.mul_mem hx hy ⟩
  mul_assoc := fun ⟨ x, _ ⟩ ⟨ y, _ ⟩ ⟨ z, _ ⟩ => SetCoe.ext (mul_assoc x y z)
  one := ⟨ 1, H.one_mem ⟩
  one_mul := fun ⟨ x, _ ⟩ => SetCoe.ext (one_mul x)
  mul_one := fun ⟨ x, _ ⟩ => SetCoe.ext (mul_one x)
  inv := fun ⟨ x, hx ⟩ => ⟨ x⁻¹, H.inv_mem hx ⟩
  inv_mul_cancel := fun ⟨ x, hx ⟩ => SetCoe.ext (inv_mul_cancel x)

class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G] [SubmonoidClass₁ S G] : Prop where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G where
  inv_mem := Subgroup₁.inv_mem

def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M where
  r := fun x y => ∃ w ∈ N, ∃ z ∈ N, x * w = y * z
  iseqv := {
    refl := fun x => ⟨ 1, N.one_mem, 1, N.one_mem, rfl ⟩
    symm := fun ⟨ w, hw, z, hz, h ⟩ => ⟨ z, hz, w, hw, h.symm ⟩
    trans := by
      rintro a b c ⟨w₁, hw₁, z₁, hz₁, hab⟩ ⟨w₂, hw₂, z₂, hz₂, hbc⟩
      use w₁ * w₂, N.mul_mem hw₁ hw₂, z₂ * z₁, N.mul_mem hz₂ hz₁
      grind
  }

/- errors -/
/- instance [CommMonoid M] : HasQuotient M (Submonoid M) where
 -   quotient' := fun N ↦ Quotient N.Setoid -/


end M8Hierarchies
