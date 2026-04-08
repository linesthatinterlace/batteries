/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

module

@[expose] public section

namespace Nat

/-- `bit b n` appends the digit `b` to the little end of the binary representation of `n`. -/
def bit (b : Bool) : Nat → Nat | 0 => b.toNat | n + 1 => bit b n + 2

/-- Efficient implementation of bit. -/
@[inline] def bitImpl (b : Bool) (n : Nat) : Nat := n <<< 1 + b.toNat

@[csimp] theorem bit_eq_bitImpl : bit = bitImpl := funext <| fun _ => funext <| fun _ => by
  fun_induction bit <;> grind [bitImpl, shiftLeft_succ]

/-- `isOdd n` returns `true` just when `n` is odd -/
def isOdd : Nat → Bool | 0 => false | 1 => true | n + 2 => n.isOdd

/-- Efficient implementation of isOdd. -/
@[inline] def isOddImpl (n : Nat) : Bool := 1 &&& n != 0

@[csimp] theorem isOdd_eq_isOddImpl : isOdd = isOddImpl := funext <| fun _ => by
  fun_induction isOdd <;> grind [isOddImpl]

/-- `isEven n` returns `true` just when `n` is even -/
def isEven : Nat → Bool | 0 => true | 1 => false | n + 2 => n.isEven

/-- Efficient implementation of isOdd. -/
@[inline] def isEvenImpl (n : Nat) : Bool := !(1 &&& n != 0)

@[csimp] theorem isEven_eq_isEvenImpl : isEven = isEvenImpl := funext <| fun _ => by
  fun_induction isEven <;> grind [isEvenImpl]

/-- `div2 n` is the greatest integer smaller than `n/2` -/
def div2 : Nat → Nat | 0 | 1 => 0 | n + 2 => n.div2 + 1

/-- Efficient implementation of div2. -/
@[inline] def div2Impl (n : Nat) : Nat := n >>> 1

@[csimp] theorem div2_eq_div2Impl : div2 = div2Impl := funext <| fun _ => by
  fun_induction div2 <;> grind [div2Impl, Nat.shiftRight_succ]

/-- A bitwise recursion principle for  natural numbers.
  We have base cases for `0` and `1`: for all other natural numbers `n + 2`,
  the case for `n.div2 + 1` suffices. -/
@[elab_as_elim, specialize]
 def binaryRec {motive : Nat → Sort u} (zero : motive 0) (one : motive 1)
    (add_two : ∀ n, motive (n.div2 + 1) → motive (n + 2)) : ∀ n, motive n
  | 0 => zero | 1 => one | n + 2 => add_two n <| (n.div2 + 1).binaryRec zero one div2
  termination_by n => n decreasing_by fun_induction div2 <;> grind

/-- Elim over the binary digits of a natural number, from least significant to most significant.
    Base cases are provided for `0`, `1`. All other numbers are folded via their binary digits. -/
@[specialize]
def binaryElim {α : Sort u} (zero one : α) (bit : Bool → α → α) : Nat → α
  | 0 => zero | 1 => one | n + 2 => bit n.isOdd <| (n.div2Impl + 1).binaryElim zero one bit
  termination_by n => n decreasing_by grind [div2Impl, shiftRight_le]

/-- `size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation -/
def size (n : Nat) : Nat := n.binaryElim 0 1 (Function.const Bool succ)

/-- `popcount n` : Returns the number of set bits in a natural number. -/
def popcount (n : Nat) : Nat := n.binaryElim 0 1 (flip (· + ·.toNat))

/-- `bitsList n` returns a list of Bools which correspond to the binary representation of n, where
the head of the list represents the least significant bit. -/
def bitsList (n : Nat) : List Bool := n.binaryElim [] [true] List.cons

/-- `ofBitsList bs` constructs a natural number from a list of bits using little endian
  convention. -/
@[inline] def ofBitsList (xs : List Bool) : Nat :=
  xs.foldr bit 0

/-- `leastBitsList n` returns, for non-zero `n`, `some l`, where `l` is a list of the bits below the
  most significant bit of `n`. It returns `none` just when `n = 0`. -/
def leastBitsList (n : Nat) : Option (List Bool) :=
  n.binaryElim none (some []) (Option.map <| List.cons ·)

/-- `ofLeastBitsList oxs` constructs a natural number from the bits below its most signficant
  bit (and is `0` just when the `Option` is empty). -/
def ofLeastBitsList (oxs : Option (List Bool)) : Nat :=
  oxs.elim 0 (Nat.add.uncurry <| ·.foldr (Prod.map (Nat.bit false) <| Nat.bit ·) (1, 0))

/-- A recursion principle over the even natural numbers. -/
@[elab_as_elim, specialize]
 def evenRec {motive : (n : Nat) → n.isEven → Sort u} (zero : motive 0 rfl)
    (succ_succ : ∀ n h, motive n h → motive (n + 2) h) :
    (n : Nat) → (hn : n.isEven) → motive n hn
  | 0, _ => zero
  | n + 2, h => succ_succ n h (evenRec zero succ_succ n h)

/-- A recursion principle over the odd natural numbers. -/
@[elab_as_elim, specialize]
 def oddRec {motive : (n : Nat) → n.isOdd → Sort u} (one : motive 1 rfl)
    (succ_succ : ∀ n h, motive n h → motive (n + 2) h) :
    (n : Nat) → (hn : n.isOdd) → motive n hn
  | 1, _ => one
  | n + 2, h => succ_succ n h (oddRec one succ_succ n h)
