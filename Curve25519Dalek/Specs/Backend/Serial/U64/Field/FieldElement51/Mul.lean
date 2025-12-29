/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs

/-! # Spec Theorem for `FieldElement51::mul`

Specification and proof for `FieldElement51::mul`.

This function computes the product of two field elements.

Source: curve25519-dalek/src/backend/serial/u64/field.rs -/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.field.FieldElement51.Mul

-- duplicated?
@[progress]
theorem m_spec (x y : U64) :
    ∃ result, mul.m x y = ok (result) ∧
    result.val = x.val * y.val := by
  unfold mul.m
  progress*
  -- BEGIN TASK
  simp [*]
  scalar_tac
  -- END TASK

/-
natural language description:

    • Computes the product of two field elements a and b in the field 𝔽_p where p = 2^255 - 19
    • The field elements are represented as five u64 limbs each

natural language specs:

    • The function always succeeds (no panic)
    • Field51_as_Nat(result) ≡ Field51_as_Nat(lhs) * Field51_as_Nat(rhs) (mod p)
-/
set_option maxHeartbeats 1000000 in
/-- **Spec and proof concerning `backend.serial.u64.field.FieldElement51.Mul.mul`**:
- No panic (always returns successfully)
- The result, when converted to a natural number, is congruent to the product of the inputs modulo p
- Input bounds: each limb < 2^54
- Output bounds: each limb < 2^52
-/
@[progress]
theorem mul_spec (lhs rhs : Array U64 5#usize)
    (hlhs : ∀ i < 5, lhs[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, rhs[i]!.val < 2 ^ 54) :
    ∃ r, mul lhs rhs = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat lhs) * (Field51_as_Nat rhs) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) := by
  unfold mul
  have := hrhs 0 (by simp);
  have := hrhs 1 (by simp);
  have := hrhs 2 (by simp);
  have := hrhs 3 (by simp);
  have := hrhs 4 (by simp);
  have := hlhs 0 (by simp);
  have := hlhs 1 (by simp);
  have := hlhs 2 (by simp);
  have := hlhs 3 (by simp);
  have := hlhs 4 (by simp);
  progress; progress; progress; progress;
  progress; progress; progress; progress;
  progress; progress; progress; progress;
  progress; progress
  · /-have : (lhs.val)[0]!.val * (rhs.val)[0]!.val ≤ (2 ^ 54 - 1) * (2 ^ 54 - 1) := by
        scalar_tac +nonLin
    have : (lhs.val)[4]!.val * (rhs).val[1]!.val ≤ (2 ^ 54 - 1) * (2 ^ 54 - 1) := by
        scalar_tac +nonLin
    --simp [*]
    -/
    simp only [*]
    ring_nf
    scalar_tac
    --ring_nf

  progress; progress; progress
  · simp only [*]
    ring_nf
    scalar_tac
  progress; progress; progress
  · simp only [*]
    ring_nf
    scalar_tac
  progress; progress; progress
  · sorry
  progress; progress; progress
  · sorry
  progress; progress
  · sorry
  progress; progress
  · sorry
  progress; progress
  · sorry

set_option maxHeartbeats 10000000 in
@[progress]
theorem mul_spec' (lhs rhs : Array U64 5#usize)
    (hlhs : ∀ i < 5, lhs[i]!.val < 2 ^ 54) (hrhs : ∀ i < 5, rhs[i]!.val < 2 ^ 54) :
    ∃ r, mul lhs rhs = ok r ∧
    Field51_as_Nat r ≡ (Field51_as_Nat lhs) * (Field51_as_Nat rhs) [MOD p] ∧
    (∀ i < 5, r[i]!.val < 2 ^ 52) := by
  unfold mul
  have := hrhs 0 (by simp);
  have := hrhs 1 (by simp);
  have := hrhs 2 (by simp);
  have := hrhs 3 (by simp);
  have := hrhs 4 (by simp);
  have := hlhs 0 (by simp);
  have := hlhs 1 (by simp);
  have := hlhs 2 (by simp);
  have := hlhs 3 (by simp);
  have := hlhs 4 (by simp);
  progress* by (simp only [*]; ring_nf; scalar_tac) -- this may work, but it's way too slow


end curve25519_dalek.backend.serial.u64.field.FieldElement51.Mul

def inBounds (a : Array U64 5#usize) := ∀ i < 5, a[i]!.val < 2 ^ 54

@[scalar_tac]
theorem inBounds_imp {a} (h0 : inBounds a) i (h : i < 5) :
    a[i]!.val < 2 ^ 54 := by sorry

example a (h0 : inBounds a) i (h : i < 5) :
    a[i]!.val < 2 ^ 54 := by
    scalar_tac
