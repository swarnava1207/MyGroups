import MyGroups.Defs
import MyGroups.Actions
import MyGroups.Homs
import MyGroups.SubGroups

universe u v
open MyGroup

def centralizer (G : Type u) [MyGroup G] (H : Set G) : Set G :=
  { g : G | ∀ a ∈ H, a * g = g * a }

def center (G : Type u) [MyGroup G] : Set G :=
  { g : G | ∀ a : G, a * g = g * a }

theorem centralizer_subgroup (G : Type u) [MyGroup G] (H : Set G) :
  SubGroup G (centralizer G H) := by
    constructor
    · simp [centralizer]
    · intro a ha
      simp [centralizer] at ha
      simp [centralizer]
      intro b hb
      have h1 : b * a * a⁻¹ = a * b * a⁻¹ := by
        rw [cancel_right]
        apply ha
        assumption
      have h2 : a ⁻¹ * b * a * a⁻¹ = a ⁻¹ * a * b * a⁻¹ := by
        rw [assoc a⁻¹ b a, assoc a⁻¹ a b]
        rw [assoc , assoc a⁻¹ (a * b) a⁻¹]
        rw [cancel_left]
        assumption
      simp at h2
      rw [h2]
    · intro a b ha hb
      simp [centralizer] at ha hb
      simp [centralizer]
      intro c hc
      rw [← assoc, ha c]
      rw [← hb c, assoc]
      assumption
      assumption

theorem center_subgroup (G : Type u) [MyGroup G] :
  SubGroup G (center G) := by
    rw [subgrp_iff]
    constructor
    · use (1 : G)
      simp [center]
    · intro g h hg hh
      simp [center] at hg hh
      simp [center]
      intro a
      rw [← assoc, hg a, assoc]
      rw [← inv_of_inv a, ← inv_of_prod h a⁻¹]
      rw [← hh a⁻¹, inv_of_prod]

instance {G : Type u} [MyGroup G] : HMul G (Set G) (Set G) where
  hMul := fun g H => { g * a | a ∈ H}

instance {G : Type u} [MyGroup G] : HMul (Set G) G (Set G) where
  hMul := fun H g => { a * g | a ∈ H}

def normalizer (G : Type u) [MyGroup G] (H : Set G) : Set G :=
  { g : G | g * H = H * g }


