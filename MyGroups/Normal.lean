import MyGroups.Defs
import MyGroups.Actions
import MyGroups.Homs
import MyGroups.SubGroups
import MyGroups.Centers


universe u
open MyGroup

def normal (G : Type u) [MyGroup G] (H : Set G) [SubGroup G H] : Prop :=
  ∀ a : G, a * H = H * a

theorem normal_normalizer (G : Type u) [MyGroup G] (H : Set G) [SubGroup G H] :
  normal G H ↔ normalizer G H = Set.univ := by
  constructor
  · intro h
    simp [normalizer]
    simp [normal] at h
    apply Set.ext
    intro x
    constructor
    · intro hx
      simp
    · intro hx
      have h₁ : x * H = H * x := by exact h x
      simp
      assumption
  · intro h
    simp [normalizer] at h
    simp [normal]
    intro a
    have h₁ : a ∈ Set.univ := by simp
    rw [← h] at h₁
    simp at h₁
    assumption

def left_coset_set {G : Type u} [MyGroup G] (H : Set G) : Set (Set G) := { g * H | g : G }

instance quotient_normal (G : Type u) [MyGroup G] (H : Set G) [SubGroup G H] (h : normal G H) :
  HasQuotient G H where
    quotient' := sorry

-- instance coset_group (G : Type u) [MyGroup G] (H : Set G) [SubGroup G H] (h : normal G H) : MyGroup (left_coset_set H) where
