/-
Copyright (c) 2025 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais
-/

module

public import Batteries.Data.Nat.Bitwise.Defs

@[expose] public section

/-! # Bitwise Lemmas

This module defines properties of the bitwise operations on natural numbers.

This file is complements `Init.Data.Nat.Bitwise.Lemmas` with properties that
are not necessary for the bitvector library.
-/

namespace Nat

/-! ### and -/

@[simp] theorem and_self_left (a b : Nat) : a &&& (a &&& b) = a &&& b := by
  apply Nat.eq_of_testBit_eq; simp

@[simp] theorem and_self_right (a b : Nat) : ((a &&& b) &&& b) = (a &&& b) := by
  apply Nat.eq_of_testBit_eq; simp

theorem and_left_comm (x y z : Nat) : x &&& (y &&& z) = y &&& (x &&& z) := by
  apply Nat.eq_of_testBit_eq; simp [Bool.and_left_comm]

theorem and_right_comm (x y z : Nat) : (x &&& y) &&& z = (x &&& z) &&& y := by
  apply Nat.eq_of_testBit_eq; simp [Bool.and_right_comm]

/-! ### or -/

@[simp] theorem or_self_left (a b : Nat) : a ||| (a ||| b) = a ||| b := by
  apply Nat.eq_of_testBit_eq; simp

@[simp] theorem or_self_right (a b : Nat) : (a ||| b) ||| b = a ||| b := by
  apply Nat.eq_of_testBit_eq; simp

theorem or_left_comm (x y z : Nat) : x ||| (y ||| z) = y ||| (x ||| z) := by
  apply Nat.eq_of_testBit_eq; simp [Bool.or_left_comm]

theorem or_right_comm (x y z : Nat) : (x ||| y) ||| z = (x ||| z) ||| y := by
  apply Nat.eq_of_testBit_eq; simp [Bool.or_right_comm]

/-! ### xor -/

theorem xor_left_comm (x y z : Nat) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  apply Nat.eq_of_testBit_eq; simp only [testBit_xor, Bool.xor_left_comm, implies_true]

theorem xor_right_comm (x y z : Nat) : (x ^^^ y) ^^^ z = (x ^^^ z) ^^^ y := by
  apply Nat.eq_of_testBit_eq; simp only [testBit_xor, Bool.xor_right_comm, implies_true]

@[simp] theorem xor_xor_cancel_left (x y : Nat) : x ^^^ (x ^^^ y) = y := by
  apply Nat.eq_of_testBit_eq; simp

@[simp] theorem xor_xor_cancel_right (x y : Nat) : (x ^^^ y) ^^^ y = x := by
  apply Nat.eq_of_testBit_eq; simp

theorem eq_of_xor_eq_zero {x y : Nat} : x ^^^ y = 0 → x = y := by
  intro h; rw [← xor_xor_cancel_left x y, h, xor_zero]

@[simp] theorem xor_eq_zero_iff {x y : Nat} : x ^^^ y = 0 ↔ x = y :=
  ⟨eq_of_xor_eq_zero, fun | rfl => Nat.xor_self _⟩

theorem xor_ne_zero_iff {x y : Nat} : x ^^^ y ≠ 0 ↔ x ≠ y := by simp

/-! ### injectivity lemmas -/

theorem xor_right_injective {x : Nat} : Function.Injective (x ^^^ ·) := by
  intro y z h; rw [← xor_xor_cancel_left x y, ← xor_xor_cancel_left x z]; simp only [h]

theorem xor_left_injective {x : Nat} : Function.Injective (· ^^^ x) := by
  intro y z h; rw [← xor_xor_cancel_right y x, ← xor_xor_cancel_right z x]; simp only [h]

@[simp] theorem xor_right_inj {x y z : Nat} : x ^^^ y = x ^^^ z ↔ y = z :=
  ⟨(xor_right_injective ·), fun | rfl => rfl⟩

@[simp] theorem xor_left_inj {x y z : Nat} : x ^^^ z = y ^^^ z ↔ x = y :=
  ⟨(xor_left_injective ·), fun | rfl => rfl⟩

theorem and_or_right_injective {m x y : Nat} : x &&& m = y &&& m → x ||| m = y ||| m → x = y := by
  intro ha ho
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Bool.and_or_inj_right_iff (m := m.testBit i)]
  simp [← testBit_and, ← testBit_or, ha, ho]

theorem and_or_right_inj {m x y : Nat} : x &&& m = y &&& m ∧ x ||| m = y ||| m ↔ x = y :=
  ⟨fun ⟨ha, ho⟩ => and_or_right_injective ha ho, fun | rfl => ⟨rfl, rfl⟩⟩

theorem and_or_left_injective {m x y : Nat} : m &&& x = m &&& y → m ||| x = m ||| y → x = y := by
  intro ha ho
  apply Nat.eq_of_testBit_eq
  intro i
  rw [← Bool.and_or_inj_left_iff (m := m.testBit i)]
  simp [← testBit_and, ← testBit_or, ha, ho]

theorem and_or_left_inj {m x y : Nat} : m &&& x = m &&& y ∧ m ||| x = m ||| y ↔ x = y :=
  ⟨fun ⟨ha, ho⟩ => and_or_left_injective ha ho, fun | rfl => ⟨rfl, rfl⟩⟩

/-! ### bodd -/

@[simp, grind =] theorem bodd_zero : bodd 0 = false := rfl
@[simp, grind =] theorem bodd_one : bodd 1 = true := rfl
@[simp, grind =] theorem bodd_add_two : bodd (n + 2) = bodd n := rfl

@[grind =] theorem bodd_succ : bodd (n + 1) = !(bodd n) := by induction n <;> grind

@[csimp]
theorem bodd_eq_boddImpl : bodd = boddImpl := by
  funext; fun_induction bodd <;> grind [boddImpl]

@[grind =] theorem bodd_val : bodd n = n.testBit 0 := congrFun bodd_eq_boddImpl n

/-! ### div2 -/

@[simp, grind =] theorem div2_zero : div2 0 = 0 := rfl
@[simp, grind =] theorem div2_one : div2 1 = 0 := rfl
@[simp, grind =] theorem div2_add_two : div2 (n + 2) = div2 n + 1 := rfl

@[grind =] theorem div2_succ : div2 (n + 1) = n.div2 + n.bodd.toNat := by induction n <;> grind

@[csimp]
theorem div2_eq_div2Impl : div2 = div2Impl := by
  funext; fun_induction div2 <;> grind [div2Impl, Nat.shiftRight_eq_div_pow]

@[grind =] theorem div2_val : div2 n = n / 2 := congrFun div2_eq_div2Impl n

/-! ### bit -/

@[simp, grind =] theorem bit_zero : bit b 0 = b.toNat := rfl
@[simp, grind =] theorem bit_succ : bit b (n + 1) = bit b n + 2 := rfl

@[csimp]
theorem bit_eq_bitImpl : bit = bitImpl := by
  funext b n; fun_induction bit <;> cases b <;> grind [bitImpl]

@[grind =] theorem bit_val : bit b n = 2 * n + b.toNat := congrFun (congrFun bit_eq_bitImpl b) n

/-! ### div2, bodd, bit -/

@[simp, grind =] theorem bodd_bit {b : Bool} (n : Nat) : (n.bit b).bodd = b := by
  fun_induction bit <;> grind [cases Bool]

@[simp, grind =] theorem div2_bit {b : Bool} (n : Nat) : (n.bit b).div2 = n := by
  fun_induction bit <;> grind [cases Bool]

@[simp, grind =] theorem bit_bodd_div2 (n : Nat) : n.div2.bit n.bodd = n := by
  fun_induction div2 <;> grind

theorem ext_div2_bodd {n m : Nat} (h0 : n.div2 = m.div2) (h1 : n.bodd = m.bodd) : n = m :=
  n.bit_bodd_div2.symm.trans (h0 ▸ h1 ▸ m.bit_bodd_div2)

theorem ext_div2_bodd_iff (n m : Nat) : n = m ↔ n.div2 = m.div2 ∧ n.bodd = m.bodd := by
  grind [ext_div2_bodd]

theorem eq_of_bit_eq (n m : Nat) {b d : Bool} (h : bit b n = bit d m) : n = m := by
  simpa using congrArg div2 h

theorem bool_eq_of_bit_eq (n m : Nat) {b d : Bool} (h : bit b n = bit d m) : b = d := by
  simpa using congrArg bodd h

theorem bit_inj (n m : Nat) (b d : Bool) : bit b n = bit d m ↔ n = m ∧ b = d := by
  grind [eq_of_bit_eq, bool_eq_of_bit_eq]

@[simp] theorem bit_eq_zero_iff : bit b n = 0 ↔ n = 0 ∧ b = false := bit_inj n 0 b false
@[simp] theorem bit_ne_zero_iff : bit b n ≠ 0 ↔ n ≠ 0 ∨ b = true := by grind [bit_eq_zero_iff]

instance [NeZero n] : NeZero (bit b n) := ⟨bit_ne_zero_iff.mpr <| Or.inl <| NeZero.ne _⟩

theorem exists_bit (n : Nat) : ∃ b m, n = bit b m := ⟨n.bodd, n.div2, n.bit_bodd_div2.symm⟩

theorem exists_div2_bodd (b : Bool) (n : Nat) : ∃ m : Nat, m.bodd = b ∧ m.div2 = n :=
  ⟨bit b n, n.bodd_bit, n.div2_bit⟩

/-! ### binaryInduction -/

section

variable {motive : Nat → Sort u} (zero : motive 0) (one : motive 1)
  (bit : ∀ n, motive (n.div2 + 1) → motive (n + 2))

@[simp, grind =] theorem binaryInduction_zero : binaryInduction zero one bit 0 = zero := by
  simp [binaryInduction]
@[simp, grind =] theorem binaryInduction_one : binaryInduction zero one bit 1 = one := by
  simp [binaryInduction]
@[simp, grind =] theorem binaryInduction_add_two : binaryInduction zero one bit (n + 2) =
    bit n (binaryInduction zero one bit (n.div2 + 1)) := by simp [binaryInduction]

end

/-! ### size -/

@[simp, grind =] theorem size_zero : size 0 = 0 := by simp [size]
@[simp, grind =] theorem size_one : size 1 = 1 := by simp [size]
@[simp, grind =] theorem size_add_two : size (n + 2) = size (n.div2 + 1) + 1 := by simp [size]

theorem size_bit_succ : size (bit b (n + 1)) = size (n + 1) + 1 := by simp
@[grind =] theorem size_bit_of_ne_zero (hn : n ≠ 0) : size (bit b n) = size n + 1 := by
  cases n <;> simp at hn ⊢
@[simp, grind =] theorem size_bit_of_neZero [NeZero n] : size (bit b n) = size n + 1 :=
  size_bit_of_ne_zero (NeZero.ne _)

@[simp, grind =] theorem size_bit_true : size (bit true n) = size n + 1 := by grind [cases Nat]

theorem size_eq_zero_iff : size n = 0 ↔ n = 0 := by grind [cases Nat]
theorem size_ne_zero_iff : size n ≠ 0 ↔ n ≠ 0 := by grind [cases Nat]

/-! ### bits -/

@[simp, grind =] theorem bits_zero : bits 0 = [] := by simp [bits]
@[simp, grind =] theorem bits_one : bits 1 = [true] := by simp [bits]
@[simp, grind =] theorem bits_add_two : bits (n + 2) = n.bodd :: bits (n.div2 + 1) := by simp [bits]

theorem bits_bit_succ : bits (bit b (n + 1)) = b :: bits (n + 1) := by simp
@[grind =] theorem bits_bit_of_ne_zero (hn : n ≠ 0) : bits (bit b n) = b :: bits n := by
  cases n <;> simp at hn ⊢
@[simp, grind =] theorem bits_bit_of_neZero [NeZero n] : bits (bit b n) = b :: bits n :=
  bits_bit_of_ne_zero (NeZero.ne _)

@[simp, grind =] theorem bits_bit_true : bits (bit true n) = true :: bits n := by grind [cases Nat]

@[simp, grind =] theorem length_bits : (bits n).length = size n := by
  induction n using binaryInduction <;> grind

@[grind =] theorem bits_eq_nil_iff : bits n = [] ↔ n = 0 := by grind [cases Nat]
theorem bits_ne_nil_iff : bits n ≠ [] ↔ n ≠ 0 := by grind

@[simp] theorem bits_succ_ne_nil : bits (n + 1) ≠ [] := by grind

theorem getLast_bits (hn : bits n ≠ []) : n.bits.getLast hn = true := by
  induction n using binaryInduction <;> grind

theorem getLast_bits_succ : (n + 1).bits.getLast bits_succ_ne_nil = true := getLast_bits _

/-! ### ofBits -/

@[simp, grind =] theorem ofBits_nil : ofBits [] = 0 := rfl
@[simp, grind =] theorem ofBits_cons : ofBits (b :: bs) = bit b (ofBits bs) := rfl

@[simp] theorem ofBits_eq_zero_iff : ofBits bs = 0 ↔ ∀ x ∈ bs, x = false := by
  induction bs
  · grind
  · simp only [List.mem_cons, forall_eq_or_imp]
    grind [bit_eq_zero_iff]

theorem ofBits_ne_zero_iff : ofBits bs ≠ 0 ↔ ∃ x ∈ bs, x = true := by simp

/-! ### bits, ofBits -/

theorem ofBits_bits (n : Nat) : ofBits (bits n) = n := by
  induction n using binaryInduction <;> grind

theorem leftInverse_ofBits_bits : Function.LeftInverse ofBits bits := ofBits_bits

theorem injective_bits : Function.Injective bits := leftInverse_ofBits_bits.injective

theorem eq_of_bits_eq (hnm : bits n = bits m) : n = m := injective_bits hnm

theorem bits_inj : bits n = bits m ↔ n = m := by grind [eq_of_bits_eq]

theorem bits_ofBits_nil : bits (ofBits []) = [] := by grind

@[grind =] theorem bits_ofBits_of_getLast_eq_true {bs : List Bool} (hbs₁ : bs ≠ [])
    (hbs₂ : bs.getLast hbs₁ = true) : bits (ofBits bs) = bs := by
  induction bs with | nil => grind | cons b' bs IH =>
    have H : ofBits bs = 0 ↔ bs = [] := by cases bs <;> grind
    grind

@[grind =] theorem bits_ofBits_of_forall_getLast_eq_true {bs : List Bool}
    (hbs : ∀ (hbs : bs ≠ []), bs.getLast hbs = true) : bits (ofBits bs) = bs := by
  induction bs <;> grind

/-! ### leastBits -/

@[simp, grind =] theorem leastBits_zero : leastBits 0 = none := by simp [leastBits]
@[simp, grind =] theorem leastBits_one : leastBits 1 = some [] := by simp [leastBits]
@[simp, grind =] theorem leastBits_add_two : leastBits (n + 2) =
    (n.div2 + 1).leastBits.map (n.bodd :: ·) := by simp [leastBits]

/-! ### ofLeastBits -/

@[simp, grind =] theorem ofLeastBits_none : ofLeastBits none = 0 := rfl
@[simp, grind =] theorem ofLeastBits_some_nil : ofLeastBits (some []) = 1 := rfl

/-
Last part is getting a nice closed form for the application to some_cons, and then showing leastBits
and ofLeastBits are inverse.
-/
