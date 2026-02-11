import LSpec
import LSpec.SlimCheck
import Clean.Circuit

open LSpec
open Circuit ProvableType

#lspec test "Nat equality" (4 ≠ 5)
#lspec test "all lt" $ ∀ n, n < 10 → n - 5 < 5
#lspec test "all lt" $ ∀ n, n < 15 → n - 10 = 0

/--
A simple bit-decomposition circuit.
It witnesses n bits and asserts their weighted sum equals the input.
-/
def bitDecomp (n : ℕ) (input : Var field (F p)) : Circuit (F p) (Var (fields n) (F p)) := do
  -- Witness n bits (using a hypothetical bit-extraction function)
  let bits ← witness (fun env => fieldToBits n (eval env input))

  -- Constraint: sum(bits[i] * 2^i) - input = 0
  let sumExpr := (Vector.mapFinRange n fun i => bits[i] * (2^i.val : F p)).foldl (· + ·) 0
  assertZero (sumExpr - input)

  pure bits
