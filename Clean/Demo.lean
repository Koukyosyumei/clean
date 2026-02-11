import LSpec
import LSpec.SlimCheck
import Clean.Circuit

open LSpec
open LSpec SlimCheck
open Circuit ProvableType

#lspec test "Nat equality" (4 ≠ 5)
#lspec test "all lt" $ ∀ n, n < 10 → n - 5 < 5
--#lspec test "all lt" $ ∀ n, n < 15 → n - 10 = 0

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace WrongCircuit

def main (input : Expression (F p)) := do
  let out <== input - 1
  input * out === 0
  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 1

  -- WRONG ASSUMPTION: This is too large
  Assumptions input := input.val < 3

  Spec input output := output.val = input.val - 1 -- Simplified spec

  -- Proofs would fail here in a real verification, but we want to TEST it.
  soundness := sorry
  completeness := sorry

def test_completeness (input : F p) : Prop :=
  let c := circuit
  -- If our (wrong) assumption holds...
  (input.val < 3) →
    -- ...then an honest prover should be able to satisfy the constraints.
    let env := (c.main (const input)).proverEnvironment [input]
    ConstraintsHold env (c.main (const input) |>.operations 0)

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

instance {p : ℕ} [Fact (Nat.Prime p)] : Repr (F p) where
  reprPrec x _ := repr (x.val)

instance : Shrinkable (F 7) where
  shrink x := (Shrinkable.shrink x.val).map fun n => (n : F 7)

instance : SampleableExt (F 7) where
  proxy := Nat                -- 代理として Nat を使用
  sample := SampleableExt.interpSample Nat  -- Nat のサンプラー（0から順に大きくなる）を利用
  interp n := (n : F 7)       -- Nat を F 7 に変換するロジック

def checkConstraintsBool (eval : Environment (F p)) : List (Operation (F p)) → Bool
  | [] => True
  | .witness _ _ :: ops => checkConstraintsBool eval ops
  | .assert e :: ops => eval e = 0 ∧ checkConstraintsBool eval ops
  | .lookup l :: ops =>
    checkConstraintsBool eval ops
  | .subcircuit s :: ops =>
    checkConstraintsBool eval ops

def test_completeness' (input : F p) : Bool :=
  if input.val < 3 then
    -- 'circuit.main' ではなく 'myCircuitMain' を直接呼び出す
    let env := (main (input)).proverEnvironment [input]
    checkConstraintsBool env (main (input) |>.operations 0)
  else
    true

#lspec check "Catching the wrong range assumption" $
  ∀ (input : F 7), test_completeness' input

#lspec check "Catching the wrong range assumption" $
  ∀ (input : F 7), input.val < 3 → (input - 1) * input = 0

end WrongCircuit
