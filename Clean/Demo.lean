import LSpec
import LSpec.SlimCheck
import Clean.Circuit

open LSpec
open Circuit ProvableType

#lspec test "Nat equality" (4 ≠ 5)
#lspec test "all lt" $ ∀ n, n < 10 → n - 5 < 5
#lspec test "all lt" $ ∀ n, n < 15 → n - 10 = 0

def main (input : Expression (F p)) := do
  let out <== input - 1
  input * out === 0
  return out

def circuit : FormalCircuit (F p) field field where
  main
  localLength _ := 2

  -- WRONG ASSUMPTION: This is too large for an n-bit circuit!
  Assumptions input := input.val < 2^(n+1)

  Spec input output := (eval env output).val = input.val -- Simplified spec

  -- Proofs would fail here in a real verification, but we want to TEST it.
  soundness := sorry
  completeness := sorry
