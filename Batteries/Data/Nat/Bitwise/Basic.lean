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

theorem bodd_val : bodd n = n.testBit 0 := congrFun bodd_eq_boddImpl n

@[grind =]
theorem testBit_zero_eq_bodd {n : Nat} : n.testBit 0 = n.bodd := bodd_val.symm

/-! ### div2 -/

@[simp, grind =] theorem div2_zero : div2 0 = 0 := rfl
@[simp, grind =] theorem div2_one : div2 1 = 0 := rfl
@[simp, grind =] theorem div2_add_two : div2 (n + 2) = div2 n + 1 := rfl

@[grind =] theorem div2_succ : div2 (n + 1) = n.div2 + n.bodd.toNat := by induction n <;> grind

@[csimp]
theorem div2_eq_div2Impl : div2 = div2Impl := by
  funext; fun_induction div2 <;> grind [div2Impl, Nat.shiftRight_eq_div_pow]

theorem div2_val : div2 n = n / 2 := congrFun div2_eq_div2Impl n

@[simp, grind _=_]
theorem testBit_div2 {n : Nat} : n.div2.testBit i = n.testBit (i + 1) :=
  (congrArg (testBit · i) div2_val).trans (testBit_div_two _ _)

/-! ### bit -/

@[simp, grind =] theorem bit_zero : bit b 0 = b.toNat := rfl
@[simp, grind =] theorem bit_succ : bit b (n + 1) = bit b n + 2 := rfl

theorem bit_false : bit false n = n + n := by fun_induction bit <;> grind

@[grind =]
theorem bit_true (n : Nat) : bit true n = bit false n + 1 := by induction n <;> grind

@[simp, grind =]
theorem bit_add (b : Bool) (n m : Nat) :
    bit b (n + m) = bit false n + bit b m := by induction m <;> grind [cases Bool]

theorem bit_add_bit (b d : Bool) (a p : Nat) :
    bit b a + bit d p = bit (b != d) (a + p + (b && d).toNat) := by cases d <;> cases b <;> grind

@[csimp]
theorem bit_eq_bitImpl : bit = bitImpl := by
  funext b n; fun_induction bit <;> cases b <;> grind [bitImpl]

theorem bit_val : bit b n = 2 * n + b.toNat := congrFun (congrFun bit_eq_bitImpl b) n

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

@[simp]
theorem bit_inj (n m : Nat) (b d : Bool) : bit b n = bit d m ↔ n = m ∧ b = d := by
  grind [eq_of_bit_eq, bool_eq_of_bit_eq]

@[simp] theorem bit_eq_zero_iff : bit b n = 0 ↔ n = 0 ∧ b = false := bit_inj n 0 b false
theorem bit_ne_zero_iff : bit b n ≠ 0 ↔ n ≠ 0 ∨ b = true := by grind [bit_eq_zero_iff]

@[grind =>]
theorem ne_zero_of_bit_ne_zero (hn : bit b n = 0) : n = 0 := by grind [bit_eq_zero_iff]

@[grind =>]
theorem bit_ne_zero_of_ne_zero (hn : n ≠ 0) : bit b n ≠ 0 := by grind [bit_eq_zero_iff]

@[simp, grind =>]
theorem bit_true_ne_zero : bit true n ≠ 0 := by grind [bit_eq_zero_iff]

instance [NeZero n] : NeZero (bit b n) := ⟨bit_ne_zero_of_ne_zero <| NeZero.ne _⟩

instance : NeZero (bit true n) := ⟨bit_true_ne_zero⟩

theorem exists_bit (n : Nat) : ∃ b m, n = bit b m := ⟨n.bodd, n.div2, n.bit_bodd_div2.symm⟩

theorem exists_div2_bodd (b : Bool) (n : Nat) : ∃ m : Nat, m.bodd = b ∧ m.div2 = n :=
  ⟨bit b n, n.bodd_bit, n.div2_bit⟩

theorem testBit_bit_zero : (bit b n).testBit 0 = b := by grind
theorem testBit_bit_add_one : (bit b n).testBit (m + 1) = n.testBit m := by grind

@[grind =]
theorem testBit_bit : (bit b n).testBit m = if m = 0 then b else n.testBit (m - 1) := by
  grind [cases Nat]


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

@[simp, grind =] theorem size_bit_true : size (bit true n) = size n + 1 := by grind [cases Nat]

@[grind =] theorem size_bit_of_ne_zero (hn : n ≠ 0) : size (bit b n) = size n + 1 := by
  cases n <;> simp at hn ⊢
@[simp] theorem size_bit_of_neZero [NeZero n] : size (bit b n) = size n + 1 :=
  size_bit_of_ne_zero (NeZero.ne _)

theorem size_bit_succ : size (bit b (n + 1)) = size (n + 1) + 1 := by simp

theorem size_eq_zero_iff : size n = 0 ↔ n = 0 := by grind [cases Nat]
theorem size_ne_zero_iff : size n ≠ 0 ↔ n ≠ 0 := by grind [cases Nat]

/-! ### bitsList -/

@[simp, grind =] theorem bitsList_zero : bitsList 0 = [] := by simp [bitsList]
@[simp, grind =] theorem bitsList_one : bitsList 1 = [true] := by simp [bitsList]
@[simp, grind =] theorem bitsList_add_two : bitsList (n + 2) = n.bodd ::
    bitsList (n.div2 + 1) := by simp [bitsList]

@[simp, grind =]
theorem getElem_bitsList (hi : i < (bitsList n).length) : (bitsList n)[i] = n.testBit i := by
  induction n using binaryInduction generalizing i <;> grind [cases Nat]

@[simp, grind =] theorem length_bitsList : (bitsList n).length = size n := by
  induction n using binaryInduction <;> grind

theorem bitsList_eq_ofFn_testBit : bitsList n = List.ofFn (n := n.size) (n.testBit ·) := by
  apply List.ext_getElem <;> simp

@[simp, grind =] theorem bitsList_bit_true : bitsList (bit true n) = true :: bitsList n := by
  grind [cases Nat]

@[grind =] theorem bitsList_bit_of_ne_zero (hn : n ≠ 0) : bitsList (bit b n) = b :: bitsList n := by
  cases n <;> simp at hn ⊢
@[simp] theorem bitsList_bit_of_neZero [NeZero n] : bitsList (bit b n) = b :: bitsList n :=
  bitsList_bit_of_ne_zero (NeZero.ne _)

theorem bitsList_bit_succ : bitsList (bit b (n + 1)) = b :: bitsList (n + 1) := by simp

@[grind =] theorem bitsList_eq_nil_iff : bitsList n = [] ↔ n = 0 := by grind [cases Nat]
theorem bitsList_ne_nil_iff : bitsList n ≠ [] ↔ n ≠ 0 := by grind

@[simp]
theorem bitsList_eq_nil_of_ne_zero (hn : n ≠ 0) : bitsList n ≠ [] := by grind
@[simp]
theorem bitsList_eq_nil_of_neZero [NeZero n] : bitsList n ≠ [] :=
  bitsList_eq_nil_of_ne_zero <| NeZero.ne _

@[simp] theorem bitsList_succ_ne_nil : bitsList (n + 1) ≠ [] := by grind

@[simp, grind =]
theorem getLast_bitsList (hn : bitsList n ≠ []) : n.bitsList.getLast hn = true := by
  induction n using binaryInduction <;> grind

theorem getLast_bitsList_of_ne_zero (hn : n ≠ 0) :
    n.bitsList.getLast (bitsList_eq_nil_of_ne_zero hn) = true := getLast_bitsList _

theorem getLast_bitsList_of_neZero {n : Nat} [NeZero n] :
    n.bitsList.getLast bitsList_eq_nil_of_neZero = true := getLast_bitsList _

theorem getLast_bitsList_succ : (n + 1).bitsList.getLast bitsList_succ_ne_nil = true :=
  getLast_bitsList _

/-! ### ofBitsList -/

@[simp, grind =] theorem ofBitsList_nil : ofBitsList [] = 0 := rfl
@[simp, grind =] theorem ofBitsList_cons : ofBitsList (b :: bs) = bit b (ofBitsList bs) := rfl

@[simp] theorem ofBitsList_eq_zero_iff : ofBitsList bs = 0 ↔ ∀ x ∈ bs, x = false := by
  induction bs
  · grind
  · simp only [List.mem_cons, forall_eq_or_imp]
    grind [bit_eq_zero_iff]

theorem ofBitsList_ne_zero_iff : ofBitsList bs ≠ 0 ↔ ∃ x ∈ bs, x = true := by simp

theorem ofBitsList_lt_two_pow : ofBitsList bs < 2 ^ bs.length := by
  induction bs <;> grind [cases Bool, bit_val]

@[grind =] theorem testBit_ofBitsList (bs : List Bool) (i : Nat) :
    (ofBitsList bs).testBit i = bs[i]?.getD false := by induction bs generalizing i <;> grind

@[simp] theorem testBit_ofBitsList_lt (bs : List Bool) (i : Nat) (h : i < bs.length) :
    (ofBitsList bs).testBit i = bs[i] := by grind

@[simp] theorem testBit_ofBitsList_ge (bs : List Bool) (i : Nat) (h : bs.length ≤ i) :
    (ofBitsList bs).testBit i = false := by grind

/-! ### bitsList, ofBitsList -/

theorem ofBitsList_bitsList (n : Nat) : ofBitsList (bitsList n) = n := by
  induction n using binaryInduction <;> grind

theorem leftInverse_ofBitsList_bitsList : Function.LeftInverse ofBitsList bitsList :=
  ofBitsList_bitsList

theorem injective_bitsList : Function.Injective bitsList :=
  leftInverse_ofBitsList_bitsList.injective

theorem eq_of_bitsList_eq (hnm : bitsList n = bitsList m) : n = m := injective_bitsList hnm

theorem bitsList_inj : bitsList n = bitsList m ↔ n = m := by grind [eq_of_bitsList_eq]

theorem bitsList_ofBitsList_nil : bitsList (ofBitsList []) = [] := by grind

@[grind =] theorem bitsList_ofBitsList_of_getLast_eq_true {bs : List Bool} (hbs₁ : bs ≠ [])
    (hbs₂ : bs.getLast hbs₁ = true) : bitsList (ofBitsList bs) = bs := by
  induction bs with | nil => grind | cons b' bs IH =>
    have H : ofBitsList bs = 0 ↔ bs = [] := by cases bs <;> grind
    grind

@[grind =] theorem bitsList_ofBitsList_of_forall_getLast_eq_true {bs : List Bool}
    (hbs : ∀ (hbs : bs ≠ []), bs.getLast hbs = true) : bitsList (ofBitsList bs) = bs := by
  induction bs <;> grind

/-! ### leastBitsList -/

@[simp, grind =] theorem leastBitsList_zero : leastBitsList 0 = none := by simp [leastBitsList]
@[simp, grind =] theorem leastBitsList_one : leastBitsList 1 = some [] := by simp [leastBitsList]
@[simp, grind =] theorem leastBitsList_add_two : leastBitsList (n + 2) =
    (n.div2 + 1).leastBitsList.map (n.bodd :: ·) := by simp [leastBitsList]

@[simp, grind =]
theorem leastBitsList_eq_some_dropLast_bitsList_of_ne_zero (hn : n ≠ 0) :
    leastBitsList n = some (bitsList n).dropLast := by
  induction n using binaryInduction <;> grind [List.dropLast_cons_of_ne_nil]

@[simp]
theorem leastBitsList_eq_some_dropLast_bitsList_of_neZero [NeZero n] :
    leastBitsList n = some n.bitsList.dropLast :=
  leastBitsList_eq_some_dropLast_bitsList_of_ne_zero (NeZero.ne _)

theorem leastBitsList_succ : leastBitsList (n + 1) = some (bitsList (n + 1)).dropLast := by grind

theorem bitsList_eq_leastBitsList_elim : bitsList n = (leastBitsList n).elim [] (· ++ [true]) := by
  cases n <;> grind [List.dropLast_concat_getLast]

@[simp] theorem leastBitsList_eq_none_iff : leastBitsList n = none ↔ n = 0 := by grind

theorem leastBitsList_ne_none_iff : leastBitsList n ≠ none ↔ n ≠ 0 := by grind

theorem leastBitsList_succ_ne_none : leastBitsList (n + 1) ≠ none := by grind

/-! ### ofLeastBitsList -/

@[simp, grind =] theorem ofLeastBitsList_none : ofLeastBitsList none = 0 := rfl
@[simp, grind =] theorem ofLeastBitsList_some_nil : ofLeastBitsList (some []) = 1 := rfl

@[simp, grind =] theorem ofLeastBitsList_some_cons :
    ofLeastBitsList (some (b :: bs)) = bit b (ofLeastBitsList (some bs)) := by
  grind [ofLeastBitsList]

@[simp]
theorem ofLeastBitsList_eq_zero_iff : ofLeastBitsList oxs = 0 ↔ oxs = none := by
  cases oxs with | none => grind | some bs => induction bs <;> grind

theorem ofLeastBitsList_ne_zero_iff : ofLeastBitsList oxs ≠ 0 ↔ oxs ≠ none := by simp

theorem ofLeastBitsList_some_ne_zero : ofLeastBitsList (some bs) ≠ 0 := by simp

instance : NeZero (ofLeastBitsList (some bs)) := ⟨ofLeastBitsList_some_ne_zero⟩

/-! ### leastBitsList, ofLeastBitsList -/

theorem ofLeastBitsList_leastBitsList (n : Nat) : ofLeastBitsList (leastBitsList n) = n := by
  induction n using binaryInduction <;> grind

theorem leastBitsList_ofLeastBitsList (oxs : Option (List Bool)) :
    leastBitsList (ofLeastBitsList oxs) = oxs := by
  cases oxs with | none => grind | some bs => induction bs <;> grind [List.dropLast_cons_of_ne_nil]

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
