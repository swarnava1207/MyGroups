import MyGroups.Actions
import MyGroups.Homs
import MyGroups.SubGroups
import MyGroups.Defs
import MyGroups.Centers
import MyGroups.Orders

universe u v
namespace MyGroup
open Classical

def cyclic (G : Type u) [MyGroup G] : Prop :=
  ∃ x : G, ∀ y : G, ∃ n : ℕ , y = x ^ n

def generator (G : Type u) [MyGroup G] (x : G) : Prop :=
  ∀ y : G, ∃ n : ℕ , y = x ^ n

theorem cyclic_abelian {G : Type u} [MyGroup G] :
  cyclic G → Abelian G := by
    intro h
    simp [Abelian]
    simp [cyclic] at h
    intro a b
    let ⟨x, hx⟩ := h
    let ⟨m , hm⟩ := hx a
    let ⟨n , hn⟩ := hx b
    rw [hm, hn]
    rw [← pow_add_on_multn, ← pow_add_on_multn]
    simp [Nat.add_comm]

def order_grp (G : Type u) [MyGroup G] [Fintype G]: ℕ := Fintype.card G

theorem gen_eq_order {G : Type u} [MyGroup G] [Fintype G] (x : G) (h : generator G x) :
  order x = order_grp G := by
    let n := order x
    let h := Fintype.equivFin G
    let s := {y : G | ∀ k : Fin n , y = x ^ (k.1)}
    have h1 : Fintype.card s = n := by sorry
    sorry

theorem order_repeat {G : Type u} [MyGroup G] [Fintype G] (x : G) (h : generator G x) :
    ∀ n : ℕ ,x ^ n = x ^ (n % order x) := by
      intro n
      let m := order x
      show x ^ n = x ^ (n % m)
      have h1 : (n % m) = n - m * (n / m):= by
        apply Nat.mod_eq_sub_mul_div
      rw [h1]
      sorry



theorem order_gcd {G : Type u} [MyGroup G] (x : G) :
    ∀ m n : ℕ , x ^ m = 1 ∧ x ^ n = 1 → x ^ (Nat.gcd m n) = 1 := by
      intro m n h
      sorry

theorem order_divides {G : Type u} [MyGroup G] (x : G) (n : ℕ) (h : order x > 0) :
  x ^ n = 1 → order x ∣ n := by
    intro h
    let m := order x
    let d := Nat.gcd n m
    have h1 : x ^ m = 1 := by apply order_pow
    have h2 : x ^ d = 1 := by apply order_gcd ; constructor <;> assumption
    by_cases n = 0
    next he => simp [he]
    next hne =>
        have h3 : d ≤ m := by
            show Nat.gcd n m ≤ m
            apply Nat.gcd_le_right
            assumption
        have h4 : d ≥ m := by
            show d ≥ order x
            simp [order]
            split
            next h5 =>
              apply Nat.find_min'
              assumption
            next h6 =>
              simp
        have h5 : d = m := by apply Nat.le_antisymm <;> assumption
        show m ∣ n
        rw [← h5]
        show Nat.gcd n m ∣ n
        simp [Nat.gcd_dvd_left]

theorem cyclic_order_iso {G : Type u} {H : Type v} [MyGroup G] [MyGroup H] [Fintype G] [Fintype H]
    (hG : cyclic G) (hH : cyclic H) : order_grp G = order_grp H → isomorphic G H := by
  let ⟨x, hx⟩ := hG
  let ⟨y, hy⟩ := hH
  intro hmain
  let f : G → H := fun a => y ^ (Nat.find (hx a))
  use f
  constructor
  · intro a b
    let m := Nat.find (hx a)
    let n := Nat.find (hx b)
    let k := Nat.find (hx (a * b))
    show y ^ k = y ^ m * y ^ n
    have : a * b = x ^ (m + n) := by
      simp [pow_add_on_multn]
      rw [Nat.find_spec (hx a), Nat.find_spec (hx b)]
    have : k = m + n := by
      apply Nat.le_antisymm
      · apply Nat.find_min'
        assumption
      · sorry
    rw [← pow_add_on_multn]
    rw [this]
  · constructor
    · intro a b
      let m := Nat.find (hx a)
      let n := Nat.find (hx b)
      intro h
      sorry
    sorry














end MyGroup
