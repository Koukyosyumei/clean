import LSpec
import LSpec.SlimCheck
import LSpec.SlimCheck.Gen
import Clean.Circuit
open Lean Elab

open LSpec
open LSpec SlimCheck
open Random
open Gen
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
-- LSpec Infrastructure for Finite Fields
---

instance {p : ℕ} [Fact (Nat.Prime p)] : Repr (F p) where
  reprPrec x _ := repr (x.val)

instance {p : ℕ} [Fact (Nat.Prime p)] : Shrinkable (F p) where
  shrink x := (Shrinkable.shrink x.val).map fun n => (n : F p)

instance {p : ℕ} [Fact (Nat.Prime p)] : SampleableExt (F p) :=
  SampleableExt.mkSelfContained (do choose (Fin p) (Fin.ofNat p 0) (Fin.ofNat p (← getSize)))

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

---
-- Property-Based Test Execution
---

def test_completeness (input : F p) : Bool :=
  -- NOTE: we cannot use lspec-check when expressions contain `sorry`.
  --       Thus, we redefine the assumption without using `circuit`.
  if input.val < 3 then
    let input_val := Expression.const input
    let env := (circuit.main input_val).proverEnvironment []
    checkConstraintsBool env (circuit.main input_val |>.operations 0)
  else
    true

macro "#lspec' " term:term : command =>
  `(#eval! LSpec.runInTermElabMAsUnit $term)

-- Run the test. SlimCheck will quickly find that 'input := 2' fails.
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
#lspec' check "Catching the wrong range assumption" $
  ∀ (input : F 7), test_completeness input

end WrongCircuit
