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

/-- A walk whose final residue must return to its starting residue. -/
def closedWalk (q : Nat) (d : Nat → Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, x, start => x == start
  | fuel + 1, j, x, start =>
      decide (Nat.Coprime x q) &&
        closedWalk q d fuel (j + 1) (nextResidue q (d j) x) start

/-- A zero coefficient fixes the next residue, so the test can begin there
without first calculating the seed for the original origin. -/
def anchorPrefix (r q : Nat) (spec : List (Nat × Nat)) : Bool :=
  match (List.range r).find? (fun j => decide (coefficient q spec j % q = 0)) with
  | none => true
  | some a =>
      walkOK q (fun j => coefficient q spec (j % r)) r (a + 1)
        (nextResidue q 0 0)

/-- At a small modulus, trying every starting residue often rejects an
assignment after just a few transitions. -/
def closedPrefix (r q : Nat) (spec : List (Nat × Nat)) : Bool :=
  (List.range q).any fun x => closedWalk q (coefficient q spec) r 0 x x

/-- The inexpensive checks are used only at moduli with measured benefits. -/
def fastPrefix (r q : Nat) (spec : List (Nat × Nat)) : Bool :=
  if q = 3 then anchorPrefix r q spec
  else if q = 5 then closedPrefix r q spec
  else true

def positionTest (r q : Nat) (spec : List (Nat × Nat)) : Bool :=
  fastPrefix r q spec &&
  walkOK q (coefficient q spec) r 0
    (seedStep q (coefficient q spec) r).1

def exactSeed (d : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => d k * exactSeed d k + 2 ^ k

/-- Reordering tokens leaves every modular coefficient unchanged. -/
theorem coefficient_perm (q : Nat) {spec spec' : List (Nat × Nat)}
    (hperm : List.Perm spec spec') (j : Nat) :
    coefficient q spec j = coefficient q spec' j := by
  induction hperm with
  | nil => rfl
  | cons tp h ih =>
      simpa only [coefficient, List.foldr_cons] using
        congrArg (fun acc : Nat =>
          if tp.2 = j then (tp.1 % q * acc) % q else acc) ih
  | swap a b spec =>
      by_cases ha : a.2 = j <;> by_cases hb : b.2 = j <;>
        simp [coefficient, ha, hb, Nat.mul_comm, Nat.mul_left_comm]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The complete modular test depends only on the multiset of tokens. -/
theorem positionTest_perm (r q : Nat) {spec spec' : List (Nat × Nat)}
    (hperm : List.Perm spec spec') :
    positionTest r q spec = positionTest r q spec' := by
  have hcoef : coefficient q spec = coefficient q spec' :=
    funext (coefficient_perm q hperm)
  simp only [positionTest, fastPrefix, anchorPrefix, closedPrefix, hcoef]

end A245211New
