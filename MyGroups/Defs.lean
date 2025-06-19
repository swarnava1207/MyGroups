import Mathlib
open Classical

universe u
class MyGroup (G : Type u) where
  op : G → G → G
  id : G
  inv : G → G
  associativity : ∀ a b c : G, op (op a b) c = op a (op b c)
  id_proposition : ∀ a : G, (op a id = a ∧ op id a = a)
  inv_left_prop : ∀ a : G, op (inv a) a = id
  inv_right_prop : ∀ a : G, op a (inv a) = id

def MyGroup.pow (G : Type u) [MyGroup G] (a : G) (n : ℕ) : G :=
  if n = 0 then id else op a (MyGroup.pow G a (n - 1))

instance (G : Type u) [MyGroup G] : Mul G where
  mul := MyGroup.op

instance (G : Type u) [MyGroup G] : One G where
  one := MyGroup.id

instance (G : Type u) [MyGroup G] : Inv G where
  inv := MyGroup.inv

instance (G : Type u) [MyGroup G] : HPow G ℕ G where
  hPow := MyGroup.pow G
namespace MyGroup

@[simp]theorem assoc {G : Type u} [MyGroup G] :
  ∀ a b c : G, (a * b) * c = a * (b * c) := by
    intro a b c
    show op (op a b) c = op a (op b c)
    exact associativity a b c

@[simp]theorem id_prop {G : Type u} [MyGroup G] :
  ∀ a : G, a * 1 = a ∧ 1 * a = a := by
    intro a
    exact id_proposition a

@[simp]theorem inv_left {G : Type u} [MyGroup G] :
  ∀ a : G, a⁻¹ * a = 1 := by
    intro a
    exact inv_left_prop a

@[simp]theorem inv_right {G : Type u} [MyGroup G] :
  ∀ a : G, a * a⁻¹ = 1 := by
    intro a
    exact inv_right_prop a

def Abelian (G : Type u) [MyGroup G] : Prop :=
  ∀ a b : G, a * b = b * a

theorem id_unique {G : Type u} [MyGroup G] :
  ∀ a : G, (∀ b :G, a * b = b ∧ b * a = b) → a = 1 :=
    by
      intro a h
      have h1 : a * 1 = 1 := (h 1).1
      have h2 : 1 * a = 1 := (h 1).2
      have h3 : a = 1 := by
        rw [← (id_prop a).1]
        exact h1
      exact h3

theorem inv_unique {G : Type u} [MyGroup G] :
  ∀ a : G , (∀ b c : G, a * b = 1 ∧ b * a = 1 ∧ a * c = 1 ∧ c * a = 1 → b = c)
    := by
        intro a
        intro b c
        intro h
        rw [← (id_prop c).1]
        have h1 : a * b = 1 := h.1
        have h2 : c * a = 1 := h.2.2.2
        rw [← h1]
        rw [← assoc c a b, h2]
        rw [(id_prop b).2]

@[simp]theorem inv_of_inv {G : Type u} [MyGroup G] :
  ∀ a : G, (a⁻¹)⁻¹ = a := by
    intro a
    have h1 : a * inv a = 1 := inv_right a
    have h2 : inv a * a = 1 := inv_left a
    have h3 : inv (inv a) * inv a = 1 := by
      apply inv_left
    have h4 : inv a * inv (inv a) = 1 := by
      apply inv_right
    apply inv_unique
    repeat (first | apply And.intro | assumption)

theorem inv_of_prod {G : Type u} [MyGroup G] :
  ∀ a b : G, (a * b)⁻¹ = b ⁻¹ * a⁻¹ := by
    intro a b
    have h1 : (b⁻¹ * a⁻¹) * (a * b) = 1 := by
      rw [assoc b⁻¹ a⁻¹ (a * b)]
      rw [← assoc a⁻¹ a b]
      simp [inv_left a, id_prop]
    have h2 : (a * b) * (b⁻¹ * a⁻¹) = 1 := by
      rw [← assoc (a * b) b⁻¹ a⁻¹]
      rw [assoc a b b⁻¹]
      simp [inv_right b, id_prop]
    have h3 : inv (a * b) * (a * b) = 1 := by
      apply inv_left
    have h4 : (a * b) * inv (a * b) = 1 := by
      apply inv_right
    apply inv_unique
    repeat (first | apply And.intro | assumption)

theorem cancel_left {G : Type u} [MyGroup G] :
  ∀ a b c : G, a * b = a * c ↔ b = c := by
    intro a b c
    constructor
    · intro h
      have h1 : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by
        rw [h]
      rw [← assoc a⁻¹ a b] at h1
      rw [← assoc a⁻¹ a c] at h1
      simp [inv_left a] at h1
      assumption
    · intro h
      rw [h]

theorem cancel_right {G : Type u} [MyGroup G] :
  ∀ a b c : G, b * a = c * a ↔ b = c := by
    intro a b c
    constructor
    · intro h
      have h1 : (b * a) * a⁻¹ = (c * a) * a⁻¹ := by
        rw [h]
      rw [assoc b a a⁻¹] at h1
      rw [assoc c a a⁻¹] at h1
      simp [inv_right a] at h1
      assumption
    · intro h
      rw [h]

@[simp]theorem self_inv_one {G : Type u} [MyGroup G] :
  (1:G)⁻¹ = 1 := by
    have h1 : 1 * 1 = (1 : G) := (id_prop (1 : G)).1
    have h2 : (1:G)⁻¹ * 1 = 1 := inv_left (1 : G)
    have h3 : 1 * (1:G)⁻¹ = 1 := inv_right (1 : G)
    apply inv_unique (1 : G)
    repeat (first | apply And.intro | assumption)

noncomputable def order {G : Type u} [MyGroup G] (a : G) : ℕ :=
  if h : ∃ n : ℕ, a^n = 1 then Nat.find h else 0

end MyGroup
