import MyGroups.Defs

universe u v
def homo {G H : Type u} [MyGroup G] [MyGroup H] (f : G -> H) : Prop :=
    ∀ a b : G , f (a * b) = f a * f b

def iso {G H : Type u} [MyGroup G] [MyGroup H] (f : G -> H) : Prop :=
    homo f ∧ Function.Bijective f

def isomorphic(G H : Type u) [MyGroup G] [MyGroup H] : Prop :=
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


