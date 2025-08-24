import MyGroups.Defs
import MyGroups.Actions
import MyGroups.Homs

universe u v
namespace MyGroup


class SubGroup (G : Type u) [MyGroup G] (H : Set G) where
  id_prop : (1 : G) ∈ H
  inv_prop : ∀ a : G, a ∈ H → a⁻¹ ∈ H
  mul_prop : ∀ a b : G, a ∈ H → b ∈ H → a * b ∈ H

theorem sub_group_id {G : Type u} [MyGroup G] {H : Set G} [SubGroup G H] : (1 : G) ∈ H := by
  exact SubGroup.id_prop
theorem sub_group_inv {G : Type u} [MyGroup G] {H : Set G} [SubGroup G H] (a : G) (ha : a ∈ H) : a⁻¹ ∈ H := by
  exact SubGroup.inv_prop a ha
theorem sub_group_mul {G : Type u} [MyGroup G] {H : Set G} [SubGroup G H] (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  exact SubGroup.mul_prop a b ha hb

instance trivial (G : Type u) [MyGroup G] : SubGroup G (Set.singleton (1 : G)) where
  id_prop := by
    exact rfl
  inv_prop := by
    intro a h
    simp [Set.singleton] at h
    simp [h]
    rfl
  mul_prop := by
    intro a b ha hb
    simp [Set.singleton] at ha
    simp [Set.singleton] at hb
    simp [ha, hb]
    rfl

instance full (G : Type u) [MyGroup G] : SubGroup G (Set.univ : Set G) where
  id_prop := by
    exact Set.mem_univ (1 : G)
  inv_prop := by
    intro a h
    exact Set.mem_univ a
  mul_prop := by
    intro a b ha hb
    exact Set.mem_univ (a * b)

theorem subgrp_iff (G : Type u) [MyGroup G] (H : Set G) :
  SubGroup G H ↔ H.Nonempty ∧ (∀ a b : G, a ∈ H → b ∈ H → a * b⁻¹ ∈ H) := by
    constructor
    · intro h
      constructor
      · use (1 : G)
        exact sub_group_id
      · intro a b ha hb
        have h1 : b⁻¹ ∈ H := sub_group_inv b hb
        apply sub_group_mul <;> assumption
    . intro h
      constructor
      · have h2 : ∃ a : G, a ∈ H := h.1
        let ⟨a, ha⟩ := h2
        rw [← inv_right a]
        apply h.2 <;> assumption
      · intro a ha
        rw [← (id_prop a).1, inv_of_prod, self_inv_one]
        apply h.2 (1 : G) a _ ha
        have h2 : ∃ a : G, a ∈ H := h.1
        let ⟨a, ha⟩ := h2
        rw [← inv_right a]
        apply h.2 <;> assumption
      · intro a b ha hb
        rw [← inv_of_inv b]
        apply h.2 a b⁻¹ ha _
        rw [← (id_prop b).1, inv_of_prod, self_inv_one]
        apply h.2 (1 : G) b _ hb
        have h2 : ∃ a : G, a ∈ H := h.1
        let ⟨a, ha⟩ := h2
        rw [← inv_right a]
        apply h.2 <;> assumption


instance product_group {G : Type u} {H : Type v} [MyGroup G] [MyGroup H] : MyGroup (G × H) where
  op := fun a b => (a.1 * b.1, a.2 * b.2)
  id := (1, 1)
  inv := fun a => (a.1⁻¹, a.2⁻¹)
  associativity := by
    intro a b c
    simp
  id_proposition := by
    intro a
    simp
  inv_left_prop := by
    intro a
    simp
  inv_right_prop := by
    intro a
    simp











end MyGroup
