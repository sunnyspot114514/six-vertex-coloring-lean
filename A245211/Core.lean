import Mathlib

namespace A245211New

/-- A modular coefficient from prime tokens and their assigned positions. -/
def coefficient (q : Nat) (spec : List (Nat × Nat)) (j : Nat) : Nat :=
  spec.foldr (fun tp acc => if tp.2 = j then (tp.1 % q * acc) % q else acc) 1

/-- The affine constant and the current power of two, both modulo q. -/
def seedStep (q : Nat) (d : Nat → Nat) : Nat → Nat × Nat
  | 0 => (0, 1)
  | k + 1 =>
      let previous := seedStep q d k
      ((d k * previous.1 + previous.2) % q, (2 * previous.2) % q)

def nextResidue (q d x : Nat) : Nat :=
  ((d * x + (q - 1)) * ((q + 1) / 2)) % q

/-- Test only the residues that an actual prime cycle would have to visit. -/
def walkOK (q : Nat) (d : Nat → Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | fuel + 1, j, x =>
      decide (Nat.Coprime x q) &&
        walkOK q d fuel (j + 1) (nextResidue q (d j) x)

def positionTest (r q : Nat) (spec : List (Nat × Nat)) : Bool :=
  walkOK q (coefficient q spec) r 0
    (seedStep q (coefficient q spec) r).1

def exactSeed (d : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => d k * exactSeed d k + 2 ^ k

end A245211New
