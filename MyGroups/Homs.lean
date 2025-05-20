import MyGroups.Defs

universe u v
def homo {G H : Type u} [MyGroup G] [MyGroup H] (f : G -> H) : Prop :=
    ∀ a b : G , f (a * b) = f a * f b

def iso {G H : Type u} [MyGroup G] [MyGroup H] (f : G -> H) : Prop :=
    homo f ∧ Function.Bijective f

def isomorphic{G H : Type u} [MyGroup G] [MyGroup H] : Prop :=
    ∃ f : G → H , iso f
