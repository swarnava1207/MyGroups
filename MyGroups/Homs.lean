import MyGroups.Defs

universe u v

def homo {G : Type u} {H : Type v} [MyGroup G] [MyGroup H] (f : G -> H) : Prop :=
    ∀ a b : G , f (a * b) = f a * f b

def iso {G : Type u} {H : Type v} [MyGroup G] [MyGroup H] (f : G -> H) : Prop :=
    homo f ∧ Function.Bijective f

def isomorphic(G : Type u) (H : Type v) [MyGroup G] [MyGroup H] : Prop :=
    ∃ f : G → H , iso f

theorem self_iso {G : Type u}[MyGroup G] : isomorphic G G := by
    use id
    apply And.intro
    · intro a b
      simp
    · apply And.intro
      · intro x y
        simp
      · intro a
        use a
        simp

theorem abelian_iso {G H : Type u} [MyGroup G] [MyGroup H] :
    isomorphic G H → (MyGroup.Abelian H →  MyGroup.Abelian G) := by
        intro h
        intro h1
        intro a b
        let ⟨f, prop⟩ := h
        have h2 : f (a * b) = f a * f b := by apply prop.1
        have h3 : f (b * a) = f b * f a := by apply prop.1
        have h4 : f (a * b) = f (b * a) := by rw [h2,h3]; apply h1
        apply prop.2.1
        assumption

open MyGroup
theorem identity_map {G : Type u} {H : Type v} [MyGroup G] [MyGroup H] (f : G -> H)
    : homo f → f (1 : G) = 1 := by
        intro h
        simp [homo] at h
        have h₁ (a : G) : (f a) * 1 = (f a) * (f 1) := by rw [← h]; simp
        have h₂ : (f 1) * 1 = (f 1) * (f 1) := h₁ 1
        rw [cancel_left] at h₂
        rw [h₂]

theorem inverse_map {G : Type u} {H : Type v} [MyGroup G] [MyGroup H] (f : G -> H)
    : homo f → (∀ a : G, f a⁻¹ = (f a)⁻¹) := by
        intro h
        intro a
        simp [homo] at h
        have h₁ : f a⁻¹ * (f a) = 1 := by rw [← h]; simp; exact identity_map f h
        have h₂ : f a * (f a⁻¹) = 1 := by rw [← h]; simp; exact identity_map f h
        have h₃ : f a * (f a)⁻¹ = 1 := by simp
        have h₄ : (f a)⁻¹ * (f a) = 1 := by simp
        apply MyGroup.inv_unique
        repeat (first | apply And.intro | assumption)


