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

def eqv_rel {G : Type u} [MyGroup G] (H : Set G) [SubGroup G H] : G → G → Prop :=
  fun a b => b⁻¹ * a ∈ H

def eqv_rel_setoid {G : Type u} [MyGroup G] (H : Set G) [SubGroup G H] : Setoid G where
  r := eqv_rel H
  iseqv :=
    {refl := by
             intro x
             simp [eqv_rel]
             exact sub_group_id ,
     symm := by
             intro x y h
             simp [eqv_rel] at h
             have h1 : x ⁻¹ * y ∈ H := by
                let a := y ⁻¹ * x
                have ha : a ∈ H := h
                have h2 : a⁻¹ = x⁻¹ * y := by rw [inv_of_prod, inv_of_inv]
                rw [← h2]
                exact sub_group_inv a ha
             simp [eqv_rel]
             assumption ,
     trans := by
              intro x y z hxy hyz
              simp [eqv_rel] at hxy hyz
              simp [eqv_rel]
              have h1 : z⁻¹ * x = (z⁻¹ * y) * (y⁻¹ * x) := by
                simp
                rw [← assoc y y⁻¹ x]
                simp
              rw [h1]
              exact sub_group_mul (z⁻¹ * y) (y⁻¹ * x) hyz hxy}


def left_coset_quotient {G : Type u} [MyGroup G] (H : Set G) [SubGroup G H] : Type u :=
  Quotient (eqv_rel_setoid H)

