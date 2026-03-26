/-
Copyright (c) YEAR NAME. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NAME
-/

module

@[expose] public section

namespace Nat

/-- `bit b n` appends the digit `b` to the little end of the binary representation of `n`. -/
def bit (b : Bool) : Nat → Nat | 0 => b.toNat | n + 1 => bit b n + 2
/-- `bodd n` returns `true` if `n` is odd -/
def bodd : Nat → Bool | 0 => false | 1 => true | n + 2 => n.bodd
/-- `div2 n` is the greatest integer smaller than `n/2` -/
def div2 : Nat → Nat | 0 | 1 => 0 | n + 2 => n.div2 + 1

/-- Efficient implementation of bit. -/
@[inline] def bitImpl (b : Bool) (n : Nat) : Nat := 2 * n + b.toNat

/-- Efficient implementation of bodd. -/
@[inline] def boddImpl (n : Nat) : Bool := 1 &&& n != 0

/-- Efficient implementation of div2. -/
@[inline] def div2Impl (n : Nat) : Nat := n >>> 1

/-- A recursion principle for `bit` representations of natural numbers.
  We have base cases for `0` and `1`: all other natural numbers are of the form
  `bit b (n + 1)` and `n + 1 < bit b (n + 1)`.-/
@[elab_as_elim, specialize]
def binaryInduction {motive : Nat → Sort u} (zero : motive 0) (one : motive 1)
    (bit : ∀ n, motive (n.div2 + 1) → motive (n + 2)) : ∀ n, motive n
  | 0 => zero | 1 => one | n + 2 => bit _ <| (n.div2 + 1).binaryInduction zero one bit
  termination_by n => n decreasing_by fun_induction div2 <;> grind

/-- `size n` : Returns the size of a natural number in
bits i.e. the length of its binary representation -/
def size (n : Nat) : Nat := n.binaryInduction 0 1 (fun _ => (· + 1))

/-- `bits n` returns a list of Bools which correspond to the binary representation of n, where
the head of the list represents the least significant bit -/
def bits (n : Nat) : List Bool := n.binaryInduction [] [true] (·.bodd :: ·)

/-- Construct a natural number from a list of bits using little endian convention. -/
@[inline] def ofBits (xs : List Bool) : Nat :=
  xs.foldr bit 0

/-- `leastBits n` returns, for non-zero `n`, `some l`, where `l` is a list of the bits below the
  most significant bit of `n`. It returns `none` just when `n = 0`. -/
def leastBits (n : Nat) : Option (List Bool) :=
  n.binaryInduction none (some []) (fun n => Option.map (n.bodd :: ·))

/-- Re-construct a natural number from the bits below its most signficant bit -/
def ofLeastBits (oxs : Option (List Bool)) : Nat :=
  oxs.elim 0 ((· + ·).uncurry <| ·.foldr (fun b => Prod.map (·.bit false) (·.bit b)) (1, 0))
