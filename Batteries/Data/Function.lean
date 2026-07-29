/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

module

@[expose] public section

/-!
# Functions

This file collects additions to the `Function` namespace.

## Transposition of values

`Function.swap a b` is the transposition exchanging the values `a` and `b`, fixing everything else.
Under `LawfulBEq` it is an involution (see `swap_swap`, `swap_comp_swap`), and hence a bijection.
-/

namespace Function

/-- `Function.swap a b` is the function that swaps `a` and `b` and leaves other values as is. -/
@[inline] def swap [BEq α] (a b i : α) : α := bif a == i then b else bif b == i then a else i

section Swap

variable {a b i : α}

section BEq

theorem swap_apply [BEq α] :
    swap a b i = bif a == i then b else bif b == i then a else i := rfl

@[simp, grind =] theorem swap_apply_of_beq [BEq α] (h₁ : a == i) : swap a b i = b := by
  grind [swap_apply]
@[simp, grind =] theorem swap_apply_of_beq_false_of_beq [BEq α] (h₁ : (a == i) = false) (h₂ : b == i) :
    swap a b i = a := by grind [swap_apply]
@[simp, grind =] theorem swap_apply_of_beq_false_of_beq_false [BEq α] (h₁ : (a == i) = false)
    (h₂ : (b == i) = false) : swap a b i = i := by grind [swap_apply]

@[grind .] theorem swap_apply_cases [BEq α] :
    a == i ∧ swap a b i = b ∨
    (a == i) = false ∧ b == i ∧ swap a b i = a ∨
    (a == i) = false ∧ (b == i) = false ∧ swap a b i = i := by grind [swap_apply]

theorem beq_or_beq_of_swap_apply_ne_self [BEq α] (h : swap a b i ≠ i) : a == i ∨ b == i := by grind

end BEq

section ReflBEq

@[simp] theorem swap_apply_left [BEq α] [ReflBEq α] : swap a b a = b := by grind
theorem swap_apply_right_of_reflBEq [BEq α] [ReflBEq α] :
    swap a b b = bif a == b then b else a := by grind

end ReflBEq

section EquivBEq

@[grind _=_] theorem swap_apply_beq [BEq α] [EquivBEq α] : (swap a b i == j) =
    (i == swap a b j) := by grind [BEq.congr_right, BEq.congr_left]

@[simp, grind =] theorem swap_beq_swap_eq [BEq α] [EquivBEq α] :
    (swap a b i == swap a b j) = (i == j) := by grind [BEq.congr_right]

@[grind =] theorem swap_beq_swap_comm [BEq α] [EquivBEq α] : swap a b i == swap b a i := by
  cases ha : a == i <;> cases hb : b == i <;> grind

theorem swap_apply_right_beq [BEq α] [EquivBEq α] : swap a b b == a := by grind

theorem swap_swap_beq [BEq α] [EquivBEq α] : swap a b (swap a b i) == i := by grind

theorem swap_flip_swap_beq [BEq α] [EquivBEq α] : swap a b (swap b a i) == i := by grind

end EquivBEq

section LawfulBEq

@[simp] theorem swap_apply_eq_left [BEq α] [LawfulBEq α] : swap a b i = a ↔ i = b := by grind
@[simp] theorem swap_apply_eq_right [BEq α] [LawfulBEq α] : swap a b i = b ↔ i = a := by grind

theorem swap_apply_right [BEq α] [LawfulBEq α] : swap a b b = a := by simp
theorem swap_apply_of_ne_of_ne [BEq α] [LawfulBEq α] (h₁ : i ≠ a)
    (h₂ : i ≠ b) : swap a b i = i := by grind

@[simp] theorem swap_inj_iff [BEq α] [LawfulBEq α] : swap a b i = swap a b j ↔ i = j := by grind

theorem swap_comm [BEq α] [LawfulBEq α] : swap a b = swap b a := by grind
@[simp, grind =] theorem flip_swap [BEq α] [LawfulBEq α] : flip swap = swap (α := α) :=
  funext fun _ => funext fun _ => swap_comm
@[simp] theorem swap_comp_swap [BEq α] [LawfulBEq α] : swap a b ∘ swap a b = id := by grind
@[simp] theorem swap_comp_flip_swap [BEq α] [LawfulBEq α] : swap a b ∘ swap b a = id := by grind
@[simp] theorem swap_swap [BEq α] [LawfulBEq α] : swap a b (swap a b i) = i := by grind
@[simp] theorem swap_flip_swap [BEq α] [LawfulBEq α] : swap a b (swap b a i) = i := by grind

theorem eq_or_eq_of_swap_apply_ne_self [BEq α] [LawfulBEq α] (h : swap a b i ≠ i) :
    i = a ∨ i = b := by grind

theorem eq_iff_forall_swap_apply_eq [BEq α] [LawfulBEq α] : a = b ↔ ∀ i, swap a b i = i :=
    ⟨by grind, fun h => swap_apply_eq_left.mp <| h _⟩

theorem exists_swap_ne_self_iff [BEq α] [LawfulBEq α] : a ≠ b ↔ ∃ i, swap a b i ≠ i :=
  ⟨fun h => ⟨_, mt swap_apply_eq_left.mp h⟩, by grind⟩

@[simp] theorem swap_self [BEq α] [LawfulBEq α] : swap a a i = i := by grind

theorem leftInverse_swap [BEq α] [LawfulBEq α] : (swap a b).LeftInverse (swap a b) := by grind
theorem rightInverse_swap [BEq α] [LawfulBEq α] : (swap a b).RightInverse (swap a b) := by grind
theorem injective_swap [BEq α] [LawfulBEq α] : (swap a b).Injective :=
  leftInverse_swap.injective
theorem surjective_swap [BEq α] [LawfulBEq α] : (swap a b).Surjective :=
  rightInverse_swap.surjective

@[grind =] theorem swap_eq_id_iff [BEq α] [LawfulBEq α] : swap a b = id ↔ a = b :=
  ⟨fun h => swap_apply_eq_left.mp (h ▸ id_eq a), by grind⟩

end LawfulBEq

end Swap

end Function
