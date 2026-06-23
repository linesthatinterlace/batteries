/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

@[expose] public section

/-!
# Lawful Boolean operations

-/

-- Stage 0 - one-operation Lawful Laws

/-- `LawfulAndOp` asserts that `&&&` is associative, commutative and idempotent. -/
class LawfulAndOp (α : Type u) [AndOp α] : Prop extends
  Std.Commutative (α := α) (· &&& ·),
  Std.Associative (α := α) (· &&& ·),
  Std.IdempotentOp (α := α) (· &&& ·)

namespace LawfulAndOp

variable {α : Type u} [AndOp α] [LawfulAndOp α]

theorem and_assoc : ∀ (a b c : α), (a &&& b) &&& c = a &&& (b &&& c) := Std.Associative.assoc
theorem and_comm : ∀ (a b : α), a &&& b = b &&& a := Std.Commutative.comm
@[simp] theorem and_self : ∀ (a : α), a &&& a = a := Std.IdempotentOp.idempotent

attribute [simp] and_self

end LawfulAndOp

/-- `LawfulOrOp` asserts that `|||` is associative, commutative and idempotent. -/
class LawfulOrOp (α : Type u) [OrOp α] : Prop extends
  Std.Commutative (α := α) (· ||| ·),
  Std.Associative (α := α) (· ||| ·),
  Std.IdempotentOp (α := α) (· ||| ·)

namespace LawfulOrOp

variable {α : Type u} [OrOp α] [LawfulOrOp α]

theorem or_assoc : ∀ (a b c : α), (a ||| b) ||| c = a ||| (b ||| c) := Std.Associative.assoc
theorem or_comm : ∀ (a b : α), a ||| b = b ||| a := Std.Commutative.comm
@[simp] theorem or_self : ∀ (a : α), a ||| a = a := Std.IdempotentOp.idempotent

end LawfulOrOp

/-- `LawfulXorOp` asserts that `^^^` is associative, commutative and cancels on the
left. Equivalently, `^^^` makes `α` an abelian group of exponent two. -/
class LawfulXorOp (α : Type u) [XorOp α] : Prop extends
  Std.Commutative (α := α) (· ^^^ ·), Std.Associative (α := α) (· ^^^ ·) where
  /-- `^^^` cancels on the left. -/
  xor_self_identity (a : α) : Std.LawfulCommIdentity (α := α) (· ^^^ ·) (a ^^^ a)

namespace LawfulXorOp

variable {α : Type u} [XorOp α]

variable [LawfulXorOp α] (a : α)

theorem xor_assoc : ∀ (a b c : α), (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := Std.Associative.assoc
theorem xor_comm : ∀ (a b : α), a ^^^ b = b ^^^ a := Std.Commutative.comm
@[simp] theorem xor_self_left_id (a b : α) : (a ^^^ a) ^^^ b = b :=
  haveI := LawfulXorOp.xor_self_identity a
  Std.LawfulLeftIdentity.left_id b
@[simp] theorem xor_self_right_id (a b : α) : b ^^^ (a ^^^ a) = b :=
  haveI := LawfulXorOp.xor_self_identity a
  Std.LawfulRightIdentity.right_id b
@[simp] theorem xor_xor_self (a b : α) : a ^^^ (a ^^^ b) = b :=
  (xor_assoc _ _ _).symm.trans (xor_self_left_id _ _)
@[simp] theorem xor_self_xor (a b : α) : (a ^^^ b) ^^^ b = a :=
 (xor_assoc _ _ _).trans (xor_self_right_id _ _)

theorem xor_self_const (a b : α) : a ^^^ a = b ^^^ b :=
  (xor_self_left_id b (a ^^^ a)).symm.trans <| (xor_self_right_id a (b ^^^ b))

end LawfulXorOp

/-- `LawfulComplement` asserts that `~~~` is involutive. -/
class LawfulComplement (α : Type u) [Complement α] : Prop where
  /-- `~~~` is involutive. -/
  not_not (a : α) : ~~~(~~~a) = a

namespace LawfulComplement

variable {α : Type u} [Complement α] [LawfulComplement α]

attribute [simp] not_not

theorem not_leftInverse_not : (~~~ · : α → α).LeftInverse (~~~ · : α → α) :=
  LawfulComplement.not_not
theorem not_rightInverse_not : (~~~ · : α → α).RightInverse (~~~ · : α → α) :=
  LawfulComplement.not_not

end LawfulComplement

--- DO NOT READ BEYOND THIS POINT

-- Stage 1 - two-operations lawful laws.


/-- `LawfulAndOrOp` asserts that `&&&` and `|||` form a distributive lattice. -/
class LawfulAndOrOp (α : Type u) [AndOp α] [OrOp α] [LawfulOrOp α] [LawfulAndOp α] : Prop where
  /-- `&&&` absorbs `|||`. -/
  and_absorb_or (a b : α) : a &&& (a ||| b) = a
  /-- `|||` absorbs `&&&`. -/
  or_absorb_and (a b : α) : a ||| (a &&& b) = a
  /-- `&&&` distributes over `|||`. -/
  and_distrib_or (a b c : α) : a &&& (b ||| c) = (a &&& b) ||| (a &&& c)


class LawfulXorOpComplement (α : Type u) [XorOp α] [Complement α] : Prop where
  not_xor (a b : α) : ~~~ (a ^^^ b) = ~~~a ^^^ b
