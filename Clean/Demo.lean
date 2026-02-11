import LSpec
import LSpec.SlimCheck
import Clean.Circuit

open LSpec
open LSpec SlimCheck
open Circuit ProvableType

/-!
## PoC: Applying LSpec to Clean Circuits for Automated Bug Detection

This file demonstrates how to use LSpec to verify the "Completeness" of a circuit
written in the Clean framework. The core idea is to find inputs that satisfy our
`Assumptions` but fail the circuit's constraints, indicating a flaw in the
specification or circuit logic.

TODO: testing the "Soundness" property
-/

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

---
-- Clean's `ConstraintsHold` is a logical Proposition (Prop), which cannot be
-- directly executed during a test.
-- We define a Bool-returning version to act as our testing oracle.
---

def ConstraintsHoldFlatBool (eval : Environment (F p)) : List (FlatOperation (F p)) → Bool
  | [] => True
  | op :: ops => match op with
    | FlatOperation.assert e => (eval e = 0) ∧ ConstraintsHoldFlatBool eval ops
    | FlatOperation.lookup l => ConstraintsHoldFlatBool eval ops -- TODO: correctly support lookup
    | _ => ConstraintsHoldFlatBool eval ops

def checkConstraintsBool (eval : Environment (F p)) : List (Operation (F p)) → Bool
  | [] => True
  | .witness _ _ :: ops => checkConstraintsBool eval ops
  | .assert e :: ops => eval e = 0 ∧ checkConstraintsBool eval ops
  | .lookup l :: ops =>
    checkConstraintsBool eval ops -- TODO: correctly support lookup
  | .subcircuit s :: ops =>
    ConstraintsHoldFlatBool eval s.ops.toFlat ∧ checkConstraintsBool eval ops

namespace WrongCircuit

---
-- The Target Circuit
-- This circuit is designed to satisfy input * (input - 1) = 0.
-- It is only satisfiable only for input values 0 and 1.
---

def main (input : Expression (F p)) := do
  let out <== input - 1
  input * out === 0
  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 1

  -- WRONG ASSUMPTION: This is too large, and input=2 cannot satisfy the constraint
  Assumptions input := input.val < 3

  Spec input output := output.val = input.val - 1 -- Simplified spec

  -- Proofs would fail here in a real verification, but we want to TEST it.
  soundness := sorry
  completeness := sorry

end WrongCircuit

---
-- LSpec Infrastructure for Finite Fields
---

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

instance {p : ℕ} [Fact (Nat.Prime p)] : Repr (F p) where
  reprPrec x _ := repr (x.val)

instance : Shrinkable (F 7) where
  shrink x := (Shrinkable.shrink x.val).map fun n => (n : F 7)

instance : SampleableExt (F 7) where
  -- for now, use Nat as a proxy type for sampling.
  proxy := Nat
  sample := SampleableExt.interpSample Nat
  interp n := (n : F 7)

---
-- Property-Based Test Execution
---

def test_completeness (input : F p) : Bool :=
  -- NOTE: we cannot use lspec-check when expressions contain `sorry`.
  --       Thus, we redefine the assumption without using `circuit`.
  if input.val < 3 then
    let env := (WrongCircuit.main (Expression.const input)).proverEnvironment []
    checkConstraintsBool env (WrongCircuit.main (input) |>.operations 0)
  else
    true

-- Run the test. SlimCheck will quickly find that 'input := 2' fails.
#lspec check "Catching the wrong range assumption" $
  ∀ (input : F 7), test_completeness input
