/-
Copyright (c) 2025 François G. Dorais, Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François G. Dorais, Wrenna Robson
-/

module

public import Batteries.Data.Nat.Bitwise.Basic

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

/-! ### isOdd -/

@[simp, grind =] theorem isOdd_zero : isOdd 0 = false := rfl
@[simp, grind =] theorem isOdd_one : isOdd 1 = true := rfl
@[simp, grind =] theorem isOdd_add_two {n} : isOdd (n + 2) = isOdd n := rfl

theorem toNat_isOdd {n} : (isOdd n).toNat = n % 2 := by
  fun_induction isOdd <;> grind

@[simp, grind =] theorem isOdd_succ {n} : isOdd (n + 1) = isEven n := by
  fun_induction isEven <;> grind

theorem isOdd_val {n} : isOdd n = n.testBit 0 := congrFun isOdd_eq_isOddImpl n

/-! ### isEven -/

@[simp, grind =] theorem isEven_zero : isEven 0 = true := rfl
@[simp, grind =] theorem isEven_one : isEven 1 = false := rfl
@[simp, grind =] theorem isEven_add_two {n} : isEven (n + 2) = isEven n := rfl

theorem toNat_isEven {n} : (isEven n).toNat = 1 - n % 2 := by
  fun_induction isEven <;> grind

@[simp, grind =] theorem isEven_succ {n} : isEven (n + 1) = isOdd n := by cases n <;> simp

theorem isEven_val {n} : isEven n = !(n.testBit 0) := congrFun isEven_eq_isEvenImpl n

/-! ### isOdd, isEven -/

@[simp, grind =]
theorem not_isOdd {n} : (!(isOdd n)) = isEven n := by
  fun_induction isOdd <;> grind

@[simp, grind =]
theorem not_isEven {n} : (!(isEven n)) = isOdd n := by grind [not_isOdd]

theorem isOdd_add {m n} : isOdd (m + n) = (isOdd m ^^ isOdd n) := by
  fun_induction isOdd n <;> try grind
  simp

theorem isOdd_mul {m n} : isOdd (m * n) = (isOdd m && isOdd n) := by
  fun_induction isOdd n <;> grind [mul_succ, isOdd_add]

theorem isEven_add {m n} : isEven (m + n) = (isEven m ^^ isOdd n) := by
  fun_induction isEven n <;> try grind
  simp

theorem isEven_mul {m n} : isEven (m * n) = (isEven m || isEven n) := by
  fun_induction isEven n <;> try grind
  simpa [succ_eq_add_one, mul_succ, isEven_add]

@[simp, grind =] theorem isOdd_eq_false_iff : isOdd n = false ↔ isEven n = true := by
  fun_induction isOdd n <;> grind
@[simp, grind =] theorem isEven_eq_false_iff : isEven n = false ↔ isOdd n = true :=  by
  fun_induction isOdd n <;> grind
@[simp] theorem isOdd_ne_iff {b} : isOdd n ≠ b ↔ isEven n = b := by grind
@[simp] theorem isEven_ne_iff {b} : isEven n ≠ b ↔ isOdd n = b := by grind

theorem isEven_or_isOdd (n : Nat) : n.isEven ∨ n.isOdd := by
  fun_induction isEven n <;> grind

@[grind =]
theorem isEven_bor_isOdd (n : Nat) : n.isEven || n.isOdd := by simpa using n.isEven_or_isOdd

@[grind =]
theorem isEven_toNat_add_isOdd_toNat (n : Nat) : n.isEven.toNat + n.isOdd.toNat = 1 := by
  fun_induction isEven n <;> grind

/-! ### div2 -/

@[simp, grind =] theorem div2_zero : div2 0 = 0 := rfl
@[simp, grind =] theorem div2_one : div2 1 = 0 := rfl
@[simp, grind =] theorem div2_add_two {n} : div2 (n + 2) = div2 n + 1 := rfl

@[grind =] theorem div2_succ {n} : div2 (n + 1) = n.div2 + n.isOdd.toNat := by
  fun_induction div2 <;> grind

theorem div2_val {n} : div2 n = n / 2 := congrFun div2_eq_div2Impl n

@[simp, grind _=_]
theorem testBit_div2 {i n : Nat} : n.div2.testBit i = n.testBit (i + 1) :=
  (congrArg (testBit · i) div2_val).trans (testBit_div_two _ _)

@[simp, grind =]
theorem div2_eq_zero_iff {n : Nat} : n.div2 = 0 ↔ n = 0 ∨ n = 1 := by fun_cases Nat.div2 <;> grind

/-! ### bit -/

@[simp, grind =] theorem bit_zero {b} : bit b 0 = b.toNat := rfl
@[simp, grind =] theorem bit_succ {b n} : bit b (n + 1) = n.bit b + 2 := rfl

@[grind =]
theorem bit_add_bit (b d : Bool) (n m : Nat) :
    bit b n + bit d m =
    bif b then bit (!d) (n + m + d.toNat) else bit d (n + m) := by
  fun_induction m.bit d
  · fun_induction n.bit b <;> grind [cases Bool]
  · grind [cases Bool]

theorem bit_add_bit_false (b : Bool) (n m : Nat) :
    bit b n + bit false m = bit b (n + m) := by grind

theorem bit_false_add_bit (b : Bool) (n m : Nat) :
    bit false n + bit b m = bit b (n + m) := by grind

theorem bit_true_add_bit (b : Bool) (n m : Nat) :
    bit true n + bit b m = bit (!b) (n + m + b.toNat) := by grind

theorem bit_add_bit_true (b : Bool) (n m : Nat) :
    bit b n + bit true m = bit (!b) (n + m + b.toNat) := by grind

theorem bit_false_add_one (n : Nat) : bit false n + 1 = bit true n := bit_false_add_bit true n 0

theorem bit_true_add_one (n : Nat) : bit true n + 1 = bit false (n + 1) := bit_true_add_bit true n 0

theorem bit_add_eq_bit_bne_add_toNat_and (b d : Bool) (n m : Nat) :
    bit b n + bit d m = bit (b != d) (n + m + (b && d).toNat) := by
  cases b <;> cases d <;> apply bit_add_bit

@[grind =] theorem bit_false {n} : bit false n = 2 * n := by fun_induction bit <;> grind
@[grind =] theorem bit_true {n} : bit true n = 2 * n + 1 := by grind [bit_false_add_one]

theorem bit_val {b n} : n.bit b = 2 * n + b.toNat := congrFun (congrFun bit_eq_bitImpl b) n

@[simp, grind =]
theorem bit_inj (n m : Nat) (b d : Bool) : n.bit b = m.bit d ↔ n = m ∧ b = d := by
  fun_induction n.bit b generalizing m <;> grind [cases Bool, cases Nat]

theorem eq_of_bit_eq (n m : Nat) {b d : Bool} (h : n.bit b = bit d m) : n = m := by
  grind

theorem bool_eq_of_bit_eq (n m : Nat) {b d : Bool} (h : n.bit b = bit d m) : b = d := by
  grind

@[simp] theorem bit_eq_zero_iff {b n} : n.bit b = 0 ↔ n = 0 ∧ b = false := bit_inj n 0 b false
theorem bit_ne_zero_iff {b n} : n.bit b ≠ 0 ↔ n ≠ 0 ∨ b = true := by grind [bit_eq_zero_iff]

@[grind =>]
theorem ne_zero_of_bit_ne_zero {b n} (hn : n.bit b = 0) : n = 0 := by grind [bit_eq_zero_iff]

@[grind =>]
theorem bit_ne_zero_of_ne_zero {b n} (hn : n ≠ 0) : n.bit b ≠ 0 := by grind [bit_eq_zero_iff]

@[grind =>]
theorem bit_true_ne_zero {n} : bit true n ≠ 0 := by grind [bit_eq_zero_iff]

instance {b} {n : Nat} [NeZero n] : NeZero (n.bit b) := ⟨bit_ne_zero_of_ne_zero <| NeZero.ne _⟩

instance {n} : NeZero (bit true n) := ⟨bit_true_ne_zero⟩

@[grind =]
theorem bit_lt_bit (n m : Nat) (b d : Bool) : bit b n < bit d m ↔ n < m + ((!b) && d).toNat := by
  fun_induction n.bit b generalizing m <;> fun_cases m.bit d <;> grind [cases Bool]

@[grind =]
theorem bit_lt_bit_of_eq (n m : Nat) (b : Bool) : bit b n < bit b m ↔ n < m := by grind [cases Bool]

@[grind =]
theorem bit_le_bit_iff_eq {b n m} : bit b n ≤ bit b m ↔ n ≤ m := by grind [Nat.le_iff_lt_or_eq]

@[grind =]
theorem zero_lt_bit_iff {b k} : 0 < bit b k ↔ 0 < k ∨ b = true := by grind

@[simp]
theorem zero_lt_bit_false {k} : 0 < bit false k ↔ 0 < k := by grind

@[simp]
theorem zero_lt_bit_true {k} : 0 < bit true k := by grind

/-! ### div2, isOdd, bit -/

@[simp, grind =] theorem isOdd_bit {b} {n : Nat} : (n.bit b).isOdd = b := by
  fun_induction bit <;> grind [cases Bool]

@[simp, grind =] theorem isEven_bit {b} {n : Nat} : (n.bit b).isEven = !b := by grind

@[simp, grind =] theorem div2_bit {b} {n : Nat} : (n.bit b).div2 = n := by
  fun_induction bit <;> grind [cases Bool]

@[simp, grind =] theorem bit_isOdd_div2 {n : Nat} : n.div2.bit n.isOdd = n := by
  fun_induction div2 <;> grind

theorem bit_isEven_div2 {n : Nat} : n.div2.bit n.isEven = if n.isOdd then n - 1 else n + 1 := by
  fun_induction div2 <;> grind

theorem ext_div2_isOdd {n m : Nat} (h0 : n.div2 = m.div2) (h1 : n.isOdd = m.isOdd) : n = m :=
  n.bit_isOdd_div2.symm.trans (h0 ▸ h1 ▸ m.bit_isOdd_div2)

theorem ext_div2_isOdd_iff (n m : Nat) : n = m ↔ n.div2 = m.div2 ∧ n.isOdd = m.isOdd := by
  grind [ext_div2_isOdd]

theorem exists_bit (n : Nat) : ∃ b m, n = bit b m := ⟨n.isOdd, n.div2, n.bit_isOdd_div2.symm⟩

theorem exists_div2_isOdd (b : Bool) (n : Nat) : ∃ m : Nat, m.isOdd = b ∧ m.div2 = n :=
  ⟨n.bit b, n.isOdd_bit, n.div2_bit⟩

theorem testBit_bit_zero {b} {n : Nat} : (n.bit b).testBit 0 = b := by grind
theorem testBit_bit_add_one {b m} {n : Nat} : (n.bit b).testBit (m + 1) = n.testBit m := by grind

@[grind =]
theorem testBit_bit {b m} {n : Nat} : (n.bit b).testBit m =
    if m = 0 then b else n.testBit (m - 1) := by grind [cases Nat]

/-! ### div2Rec -/

section

variable {motive : Nat → Sort u} (zero : motive 0) (one : motive 1)
  (bit : ∀ n, motive (n.div2 + 1) → motive (n + 2))

@[simp, grind =] theorem div2Rec_zero : div2Rec zero one bit 0 = zero := by simp [div2Rec]
@[simp, grind =] theorem div2Rec_one : div2Rec zero one bit 1 = one := by simp [div2Rec]
@[simp, grind =] theorem div2Rec_add_two {n} : div2Rec zero one bit (n + 2) =
    bit n (div2Rec zero one bit (n.div2 + 1)) := by simp [div2Rec]

theorem div2Rec_bit_zero {b} :
    div2Rec (motive := motive) zero one bit (Nat.bit b 0) =
    if h : b = true then h ▸ one else b.of_not_eq_true h ▸ zero := by grind

theorem div2Rec_bit_add_two {b} {n : Nat} :
    div2Rec (motive := motive) zero one bit (n.bit b + 2) =
    bit (n.bit b) (n.div2_bit.symm ▸ div2Rec zero one bit (n + 1)) := by grind

end

/-! ### bitElim -/

section

variable {α} {zero : α} {one : α} {bit : Bool → α → α}

@[simp, grind =] theorem bitElim_zero : bitElim zero one bit 0 = zero := by simp [bitElim]
@[simp, grind =] theorem bitElim_one : bitElim zero one bit 1 = one := by simp [bitElim]
@[simp, grind =] theorem bitElim_add_two {n} : bitElim zero one bit (n + 2) =
    bit n.isOdd (bitElim zero one bit (n.div2 + 1)) := by simp [bitElim, div2_eq_div2Impl]

theorem bitElim_bit {b n} :
    bitElim zero one bit (n.bit b) = if n = 0 then bif b then one else zero else
    bit b (bitElim zero one bit n) := by grind [cases Nat]

theorem bitElim_succ {n} :
    bitElim zero one bit (n + 1) = if n = 0 then one else
    bit n.isEven (bitElim zero one bit (n.div2 + n.isOdd.toNat)) := by
  cases n with | zero => grind | succ n => cases n.isEven_or_isOdd <;> grind

end

theorem bitElim_zero_one_bit_apply (n : Nat) : bitElim 0 1 bit n = n := by
  induction n using div2Rec <;> grind

theorem bitElim_zero_one_bit : bitElim 0 1 bit = id := funext bitElim_zero_one_bit_apply

/-! ### size -/

@[simp, grind =] theorem size_zero : size 0 = 0 := by simp [size]
@[simp, grind =] theorem size_one : size 1 = 1 := by simp [size]
@[simp, grind =] theorem size_add_two {n} : size (n + 2) = size (n.div2 + 1) + 1 := by simp [size]

@[grind =]
theorem size_succ {n} : size (n + 1) = if n = 0 then 1 else size (n.div2 + n.isOdd.toNat) + 1 :=
  bitElim_succ

theorem size_eq_zero_iff {n} : size n = 0 ↔ n = 0 := by grind [cases Nat]
theorem size_ne_zero_iff {n} : size n ≠ 0 ↔ n ≠ 0 := by grind [cases Nat]

@[grind =>]
theorem size_ne_zero_of_ne_zero {n} (hn : n ≠ 0) : size n ≠ 0 :=
  size_ne_zero_iff.mpr hn

instance {n} [NeZero n] : NeZero (size n) := ⟨size_ne_zero_of_ne_zero <| NeZero.ne _⟩

theorem size_succ_ne_zero {n} : size (n + 1) ≠ 0 := NeZero.ne _

@[grind =]
theorem size_bit {b n} : size (n.bit b) = if n = 0 then b.toNat else size n + 1 := bitElim_bit

theorem size_bit_zero {b} : size (bit b 0) = b.toNat := by grind

@[simp] theorem size_bit_true {n} : size (bit true n) = size n + 1 := by grind

theorem size_bit_of_ne_zero {b n} (hn : n ≠ 0) : size (n.bit b) = size n + 1 := by grind
@[simp] theorem size_bit_of_neZero {b n} [NeZero n] : size (n.bit b) = size n + 1 :=
  size_bit_of_ne_zero (NeZero.ne _)

theorem size_bit_add_two {b n} : size (n.bit b + 2) = size (n + 1) + 1 := by simp

/-! ### popcount -/

@[simp, grind =] theorem popcount_zero : popcount 0 = 0 := by simp [popcount]
@[simp, grind =] theorem popcount_one : popcount 1 = 1 := by simp [popcount]
@[simp, grind =] theorem popcount_add_two {n} : popcount (n + 2) =
    popcount (n.div2 + 1) + n.isOdd.toNat := by simp [popcount, flip]

@[grind =]
theorem popcount_succ {n} : popcount (n + 1) = if n = 0 then 1 else
    popcount (n.div2 + n.isOdd.toNat) + n.isEven.toNat := bitElim_succ

@[simp, grind =]
theorem popcount_bit {b n} : popcount (n.bit b) = popcount n + b.toNat :=
  calc  _ = if n = 0 then b.toNat else popcount n + b.toNat := bitElim_bit
        _ = _ := by grind

theorem popcount_eq_zero_iff {n} : popcount n = 0 ↔ n = 0 := by
  induction n using div2Rec <;> grind

theorem popcount_ne_zero_iff {n} : popcount n ≠ 0 ↔ n ≠ 0 := by
  grind [popcount_eq_zero_iff]

@[grind =>]
theorem popcount_ne_zero_of_ne_zero {n} (hn : n ≠ 0) : popcount n ≠ 0 :=
  popcount_ne_zero_iff.mpr hn

instance {n} [NeZero n] : NeZero (popcount n) := ⟨popcount_ne_zero_of_ne_zero <| NeZero.ne _⟩

theorem popcount_succ_ne_zero {n} : popcount (n + 1) ≠ 0 := NeZero.ne _

@[grind .] theorem popcount_le_size {n} : popcount n ≤ size n := by
  induction n using div2Rec <;> grind

/-! ### bitsList -/

@[simp, grind =] theorem bitsList_zero : bitsList 0 = [] := by simp [bitsList]
@[simp, grind =] theorem bitsList_one : bitsList 1 = [true] := by simp [bitsList]
@[simp, grind =] theorem bitsList_add_two {n} : bitsList (n + 2) = n.isOdd ::
    bitsList (n.div2 + 1) := by simp [bitsList]

@[grind =]
theorem bitsList_succ {n} : bitsList (n + 1) = if n = 0 then [true] else
  n.isEven :: bitsList (n.div2 + n.isOdd.toNat) := bitElim_succ

theorem head_bitsList {n : Nat} (hn : n.bitsList ≠ []) : n.bitsList.head hn = n.isOdd := by
  cases n <;> grind

theorem head?_bitsList {n : Nat} : n.bitsList.head? = (Option.guard (· != 0) n).map isOdd := by
  cases n <;> grind

@[grind =]
theorem bitsList_bit {b n} : bitsList (n.bit b) =
    if n = 0 then bif b then [true] else [] else b :: n.bitsList := bitElim_bit

@[grind =]
theorem bitsList_div2 {n : Nat} : n.div2.bitsList = n.bitsList.tail := by
  cases n <;> grind

theorem bitsList_bits_of_zero_imp_true (n : Nat) (b : Bool) (hn : n = 0 → b = true) :
    (n.bit b).bitsList = b :: n.bitsList := by grind

theorem bitsList_bit_zero {b} : bitsList (bit b 0) = bif b then [true] else [] := by grind

@[simp] theorem bitsList_bit_true {n} : bitsList (bit true n) = true :: bitsList n := by
  grind [cases Nat]

theorem bitsList_bit_of_ne_zero {b n} (hn : n ≠ 0) : bitsList (n.bit b) = b :: bitsList n := by
  grind

@[simp] theorem bitsList_bit_of_neZero {b n} [NeZero n] : bitsList (n.bit b) = b :: bitsList n :=
  bitsList_bit_of_ne_zero (NeZero.ne _)

theorem bitsList_bit_add_two {b n} : bitsList (n.bit b + 2) = b :: bitsList (n + 1) := by simp

@[simp] theorem bitsList_succ_ne_nil {n} : bitsList (n + 1) ≠ [] := by grind

@[grind =] theorem bitsList_eq_nil_iff {n} : bitsList n = [] ↔ n = 0 := by grind [cases Nat]
theorem bitsList_ne_nil_iff {n} : bitsList n ≠ [] ↔ n ≠ 0 := by grind

@[grind =>] theorem bitsList_eq_nil_of_ne_zero {n} (hn : n ≠ 0) : bitsList n ≠ [] := by grind

@[simp]
theorem bitsList_eq_nil_of_neZero {n} [NeZero n] : bitsList n ≠ [] :=
  bitsList_eq_nil_of_ne_zero <| NeZero.ne _

@[simp, grind =]
theorem getElem_bitsList {i n} (hi : i < (bitsList n).length) : (bitsList n)[i] = n.testBit i := by
  induction n using div2Rec generalizing i <;> grind [cases Nat, isOdd_val.symm]

@[simp, grind =] theorem length_bitsList {n} : (bitsList n).length = size n := by
  induction n using div2Rec <;> grind

theorem bitsList_eq_ofFn_testBit {n} : bitsList n = List.ofFn (n := n.size) (n.testBit ·) := by
  apply List.ext_getElem <;> simp

@[simp, grind =]
theorem getLast_bitsList {n} (hn : bitsList n ≠ []) : n.bitsList.getLast hn = true := by
  induction n using div2Rec <;> grind

theorem getLast_bitsList_of_ne_zero {n} (hn : n ≠ 0) :
    n.bitsList.getLast (bitsList_eq_nil_of_ne_zero hn) = true := getLast_bitsList _

theorem getLast_bitsList_of_neZero {n : Nat} [NeZero n] :
    n.bitsList.getLast bitsList_eq_nil_of_neZero = true := getLast_bitsList _

theorem getLast_bitsList_succ {n} : (n + 1).bitsList.getLast bitsList_succ_ne_nil = true :=
  getLast_bitsList _

theorem count_true_bitsList {n : Nat} : n.bitsList.count true = n.popcount := by
  induction n using div2Rec <;> grind

theorem count_false_bitsList {n : Nat} : n.bitsList.count false = n.size - n.popcount := by
  apply Nat.eq_sub_of_add_eq
  simp only [List.count_eq_countP, ← count_true_bitsList, ← length_bitsList,
  List.length_eq_countP_add_countP (·), beq_false, beq_true]
  grind

/-! ### ofBitsList -/

@[simp, grind =] theorem ofBitsList_nil : ofBitsList [] = 0 := rfl
@[simp, grind =] theorem ofBitsList_cons {b bs} : ofBitsList (b :: bs) = bit b (ofBitsList bs) :=
  rfl

@[simp] theorem ofBitsList_eq_zero_iff {bs} : ofBitsList bs = 0 ↔ true ∉ bs := by
  induction bs <;> grind

@[grind .]
theorem ofBitsList_ne_zero_iff {bs} : ofBitsList bs ≠ 0 ↔ true ∈ bs := by simp

@[grind .]
theorem true_mem_of_ne_zero_ofBitsList {bs} (h : ofBitsList bs ≠ 0) : true ∈ bs := by simpa using h

@[grind .]
theorem true_mem_of_neZero_ofBitsList {bs} [NeZero (ofBitsList bs)] : true ∈ bs :=
  true_mem_of_ne_zero_ofBitsList (NeZero.ne _)

theorem ne_zero_ofBitsList_of_true_mem {bs} (h : true ∈ bs) : ofBitsList bs ≠ 0 := by simpa using h

theorem ofBitsList_replicate_false {n} : ofBitsList (List.replicate n false) = 0 := by
  induction n <;> grind [cases Bool]

theorem ofBitsList_replicate_true {n} : ofBitsList (List.replicate n true) = 2^n - 1 := by
  induction n <;> grind

theorem ofBitsList_lt_two_pow {bs} : ofBitsList bs < 2 ^ bs.length := by
  induction bs <;> grind [cases Bool]

@[grind =] theorem testBit_ofBitsList (bs : List Bool) (i : Nat) :
    (ofBitsList bs).testBit i = bs[i]?.getD false := by induction bs generalizing i <;> grind

@[simp] theorem testBit_ofBitsList_lt (bs : List Bool) (i : Nat) (h : i < bs.length) :
    (ofBitsList bs).testBit i = bs[i] := by grind

@[simp] theorem testBit_ofBitsList_ge (bs : List Bool) (i : Nat) (h : bs.length ≤ i) :
    (ofBitsList bs).testBit i = false := by grind

/-! ### bitsList, ofBitsList -/

@[grind =]
theorem ofBitsList_bitsList (n : Nat) : ofBitsList (bitsList n) = n := by
  induction n using div2Rec <;> grind

theorem leftInverse_ofBitsList_bitsList : Function.LeftInverse ofBitsList bitsList :=
  ofBitsList_bitsList

theorem injective_bitsList : Function.Injective bitsList :=
  leftInverse_ofBitsList_bitsList.injective

theorem eq_of_bitsList_eq {n m} (hnm : bitsList n = bitsList m) : n = m := injective_bitsList hnm

theorem bitsList_inj {n m} : bitsList n = bitsList m ↔ n = m := by grind [eq_of_bitsList_eq]

@[grind =] theorem bitsList_ofBitsList_of_forall_getLast_eq_true {bs : List Bool}
    (hbs : (hbs : bs ≠ []) → bs.getLast hbs = true) : bitsList (ofBitsList bs) = bs := by
  induction bs <;> grind

theorem bitsList_ofBitsList_nil : bitsList (ofBitsList []) = [] := by grind

theorem bitsList_ofBitsList_concat_true {bs : List Bool} :
    bitsList (ofBitsList (bs ++ [true])) = bs ++ [true] := by grind

theorem bitsList_ofBitsList_of_getLast_eq_true {bs : List Bool} (hbs₁ : bs ≠ [])
    (hbs₂ : bs.getLast hbs₁ = true) : bitsList (ofBitsList bs) = bs := by grind

/-! ### leastBitsList -/

@[simp, grind =] theorem leastBitsList_zero : leastBitsList 0 = none := by simp [leastBitsList]
@[grind =] theorem leastBitsList_one : leastBitsList 1 = some [] := by simp [leastBitsList]
@[simp, grind =] theorem leastBitsList_add_two {n} : leastBitsList (n + 2) =
    (n.div2 + 1).leastBitsList.map (n.isOdd :: ·) := by simp [leastBitsList]

@[grind =]
theorem leastBitsList_eq {n} :
    leastBitsList n = if n = 0 then none else some (bitsList n).dropLast := by
  induction n using div2Rec <;> grind [List.dropLast_cons_of_ne_nil]

theorem leastBitsList_eq_of_ne_zero {n} (hn : n ≠ 0) :
    leastBitsList n = some (bitsList n).dropLast := by grind

@[simp]
theorem leastBitsList_eq_of_neZero {n} [NeZero n] :
    leastBitsList n = some n.bitsList.dropLast :=
  leastBitsList_eq_of_ne_zero (NeZero.ne _)

@[simp] theorem leastBitsList_eq_none_iff {n} : leastBitsList n = none ↔ n = 0 := by grind

theorem leastBitsList_ne_none_iff {n} : leastBitsList n ≠ none ↔ n ≠ 0 := by grind

theorem leastBitsList_succ_ne_none {n} : leastBitsList (n + 1) ≠ none := by grind

theorem leastBitsList_succ {n} : leastBitsList (n + 1) = some (bitsList (n + 1)).dropLast := by
  grind

theorem bitsList_eq {n} : bitsList n = (leastBitsList n).elim [] (· ++ [true]) := by
  grind [List.dropLast_concat_getLast]

@[grind =]
theorem leastBitsList_bit {b n} : leastBitsList (n.bit b) =
    if n = 0 then bif b then some [] else none else some (b :: (bitsList n).dropLast) := by
  grind [cases Nat]

theorem leastBitsList_bit_zero {b} :
    leastBitsList (bit b 0) = bif b then some [] else none := by grind

theorem leastBitsList_bit_true {n} : leastBitsList (bit true n) =
    if n = 0 then some [] else (leastBitsList n).map (true :: ·) := by grind

/-! ### ofLeastBitsList -/

@[simp, grind =] theorem ofLeastBitsList_none : ofLeastBitsList none = 0 := rfl
@[simp, grind =] theorem ofLeastBitsList_some_nil : ofLeastBitsList (some []) = 1 := rfl
@[simp, grind =] theorem ofLeastBitsList_some_cons :
    ofLeastBitsList (some (b :: bs)) = bit b (ofLeastBitsList (some bs)) := by
  grind [ofLeastBitsList]

@[grind =]
theorem ofLeastBitsList_eq {oxs} : ofLeastBitsList oxs =
    oxs.elim 0 (ofBitsList ∘ (· ++ [true])) := by
  cases oxs with | none => grind | some bs => induction bs <;> grind

@[simp]
theorem ofLeastBitsList_eq_zero_iff {oxs} : ofLeastBitsList oxs = 0 ↔ oxs = none := by
  grind [cases Option]

theorem ofLeastBitsList_ne_zero_iff {oxs} : ofLeastBitsList oxs ≠ 0 ↔ oxs ≠ none := by simp

theorem ofLeastBitsList_some_ne_zero {bs} : ofLeastBitsList (some bs) ≠ 0 := by simp

instance : NeZero (ofLeastBitsList (some bs)) := ⟨ofLeastBitsList_some_ne_zero⟩

/-! ### leastBitsList, ofLeastBitsList -/

theorem ofLeastBitsList_leastBitsList (n : Nat) : ofLeastBitsList (leastBitsList n) = n := by
  grind [List.dropLast_concat_getLast]

theorem leastBitsList_ofLeastBitsList (oxs : Option (List Bool)) :
    leastBitsList (ofLeastBitsList oxs) = oxs := by grind [cases Option]

theorem leftInverse_ofLeastBitsList_leastBitsList :
    Function.LeftInverse ofLeastBitsList leastBitsList := ofLeastBitsList_leastBitsList

theorem injective_leastBitsList : Function.Injective leastBitsList :=
  leftInverse_ofLeastBitsList_leastBitsList.injective

theorem rightInverse_ofLeastBitsList_leastBitsList :
    Function.RightInverse ofLeastBitsList leastBitsList := leastBitsList_ofLeastBitsList

theorem injective_ofLeastBitsList : Function.Injective ofLeastBitsList :=
  rightInverse_ofLeastBitsList_leastBitsList.injective

theorem leastBitsList_inj : leastBitsList n = leastBitsList m ↔ n = m :=
  injective_leastBitsList.eq_iff

theorem ofLeastBitsList_inj : ofLeastBitsList oxs = ofLeastBitsList oys ↔ oxs = oys :=
  injective_ofLeastBitsList.eq_iff
