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
/-- `isOdd n` returns `true` just when `n` is odd -/
def isOdd : Nat → Bool | 0 => false | 1 => true | n + 2 => n.isOdd
/-- `isEven n` returns `true` just when `n` is even -/
def isEven : Nat → Bool | 0 => true | 1 => false | n + 2 => n.isEven
/-- `div2 n` is the greatest integer smaller than `n/2` -/
def div2 : Nat → Nat | 0 | 1 => 0 | n + 2 => n.div2 + 1

/-- Efficient implementation of bit. -/
@[inline] def bitImpl (b : Bool) (n : Nat) : Nat := 2 * n + b.toNat

/-- Efficient implementation of isOdd. -/
@[inline] def isOddImpl (n : Nat) : Bool := 1 &&& n != 0

/-- Efficient implementation of isOdd. -/
@[inline] def isEvenImpl (n : Nat) : Bool := !(1 &&& n != 0)

/-- Efficient implementation of div2. -/
@[inline] def div2Impl (n : Nat) : Nat := n >>> 1

/-- A recursion principle for `bit` representations of natural numbers.
  We have base cases for `0` and `1`: all other natural numbers are of the form
  `bit b (n + 1)` and `n + 1 < bit b (n + 1)`.-/
@[elab_as_elim, specialize]
 def binaryInduction {motive : Nat → Sort u} (zero : motive 0) (one : motive 1)
    (bit : ∀ n, motive (n.div2 + 1) → motive (n + 2)) : ∀ n, motive n
  | 0 => zero | 1 => one | n + 2 => bit n <| (n.div2 + 1).binaryInduction zero one bit
  termination_by n => n decreasing_by fun_induction div2 <;> grind

/-- Elim over the binary digits of a natural number, from least significant to most significant.
  Base cases are provided for `0` and `1`; all other numbers are folded via their `bit` digits. -/
def binaryElim {α : Sort u} (zero one : α) (bit : Bool → α → α) : Nat → α
  | 0 => zero | 1 => one | n + 2 => bit n.isOdd <| (n.div2Impl + 1).binaryElim zero one bit
  termination_by n => n decreasing_by grind [div2Impl, shiftRight_le]

/-- `size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation -/
def size (n : Nat) : Nat := n.binaryElim 0 1 (Function.const Bool succ)

/-- `bits n` returns a list of Bools which correspond to the binary representation of n, where
the head of the list represents the least significant bit. -/
def bitsList (n : Nat) : List Bool := n.binaryElim [] [true] List.cons

/-- Construct a natural number from a list of bits using little endian convention. -/
@[inline] def ofBitsList (xs : List Bool) : Nat :=
  xs.foldr bit 0

/-- `leastBitsList n` returns, for non-zero `n`, `some l`, where `l` is a list of the bits below the
  most significant bit of `n`. It returns `none` just when `n = 0`. -/
def leastBitsList (n : Nat) : Option (List Bool) :=
  n.binaryElim none (some []) (Option.map <| List.cons ·)

/-- Re-construct a natural number from the bits below its most signficant bit. -/
def ofLeastBitsList (oxs : Option (List Bool)) : Nat :=
  oxs.elim 0 (Nat.add.uncurry <| ·.foldr (Prod.map (Nat.bit false) <| Nat.bit ·) (1, 0))

/-- `popcount n` : Returns the number of set bits in a natural number. -/
def popcount (n : Nat) : Nat := n.binaryElim 0 1 (flip (· + ·.toNat))
