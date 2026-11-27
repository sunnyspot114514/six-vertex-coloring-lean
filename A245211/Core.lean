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
def legacyFastPrefix (r q : Nat) (spec : List (Nat × Nat)) : Bool :=
  if q = 3 then anchorPrefix r q spec
  else if q = 5 then closedPrefix r q spec
  else true

/-- A bounded minimum computed from a short list of candidate positions. -/
def minChoice (r : Nat) (P : Nat → Bool) (xs : List Nat) : Nat :=
  xs.foldr (fun j acc => if P j then Nat.min j acc else acc) r

theorem minChoice_le (r : Nat) (P : Nat → Bool) (xs : List Nat) :
    minChoice r P xs ≤ r := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      simp only [minChoice, List.foldr_cons]
      split
      · exact Nat.le_trans (Nat.min_le_right _ _) ih
      · exact ih

theorem minChoice_le_mem (r : Nat) (P : Nat → Bool) (xs : List Nat) :
    ∀ j ∈ xs, P j = true → minChoice r P xs ≤ j := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      intro j hj hP
      simp only [List.mem_cons] at hj
      change (if P x then Nat.min x (minChoice r P xs) else minChoice r P xs) ≤ j
      by_cases hx : P x = true
      · simp only [hx, ite_true]
        rcases hj with rfl | hj
        · exact Nat.min_le_left _ _
        · exact Nat.le_trans (Nat.min_le_right _ _) (ih j hj hP)
      · simp only [hx, Bool.false_eq_true, ite_false]
        rcases hj with rfl | hj
        · exact False.elim (hx hP)
        · exact ih j hj hP

theorem minChoice_selected (r : Nat) (P : Nat → Bool) (xs : List Nat) :
    minChoice r P xs = r ∨
      minChoice r P xs ∈ xs ∧ P (minChoice r P xs) = true := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      have hstep : minChoice r P (x :: xs) =
          if P x then Nat.min x (minChoice r P xs) else minChoice r P xs := rfl
      simp only [hstep]
      by_cases hx : P x = true
      · simp only [hx, ite_true]
        by_cases hle : x ≤ minChoice r P xs
        · simpa only [Nat.min_eq_left hle] using
            (Or.inr ⟨List.mem_cons_self, hx⟩ :
              x = r ∨ x ∈ x :: xs ∧ P x = true)
        · have hge : minChoice r P xs ≤ x := by omega
          have he : Nat.min x (minChoice r P xs) = minChoice r P xs :=
            Nat.min_eq_right hge
          rw [he]
          exact ih.imp_right (fun h => ⟨List.mem_cons_of_mem x h.1, h.2⟩)
      · simp only [hx, ite_false]
        exact ih.imp_right (fun h => ⟨List.mem_cons_of_mem x h.1, h.2⟩)

theorem coefficient_one_of_absent (q : Nat) (spec : List (Nat × Nat)) (j : Nat)
    (habs : ∀ tp ∈ spec, tp.2 ≠ j) : coefficient q spec j = 1 := by
  revert habs
  induction spec with
  | nil => intro _; rfl
  | cons tp spec ih =>
      intro habs
      have ht : tp.2 ≠ j := habs tp (by simp)
      have hs : ∀ u ∈ spec, u.2 ≠ j := by
        intro u hu
        exact habs u (by simp [hu])
      change (if tp.2 = j then (tp.1 % q * coefficient q spec j) % q
        else coefficient q spec j) = 1
      simpa only [ht, ite_false] using ih hs

theorem zero_coefficient_mem_positions (q : Nat) (hq : 1 < q)
    (spec : List (Nat × Nat)) (j : Nat)
    (hz : coefficient q spec j % q = 0) : j ∈ spec.map Prod.snd := by
  by_cases hm : j ∈ spec.map Prod.snd
  · exact hm
  · have hone : coefficient q spec j = 1 := coefficient_one_of_absent q spec j (by
      intro tp ht heq
      apply hm
      exact List.mem_map.mpr ⟨tp, ht, heq⟩)
    rw [hone, Nat.mod_eq_of_lt hq] at hz
    omega

def canonicalAnchor (r q : Nat) (spec : List (Nat × Nat)) : Nat :=
  minChoice r (fun j => decide (j < r ∧ coefficient q spec j % q = 0))
    (spec.map Prod.snd)

theorem canonicalAnchor_le (r q : Nat) (spec : List (Nat × Nat)) :
    canonicalAnchor r q spec ≤ r := minChoice_le _ _ _

theorem canonicalAnchor_valid (r q : Nat) (spec : List (Nat × Nat))
    (h : canonicalAnchor r q spec < r) :
    coefficient q spec (canonicalAnchor r q spec) % q = 0 := by
  rcases minChoice_selected r
      (fun j => decide (j < r ∧ coefficient q spec j % q = 0))
      (spec.map Prod.snd) with heq | hmem
  · change canonicalAnchor r q spec = r at heq
    omega
  · exact (of_decide_eq_true hmem.2).2

theorem canonicalAnchor_le_zero (r q : Nat) (hq : 1 < q)
    (spec : List (Nat × Nat)) (j : Nat) (hj : j < r)
    (hz : coefficient q spec j % q = 0) : canonicalAnchor r q spec ≤ j := by
  apply minChoice_le_mem
  · exact zero_coefficient_mem_positions q hq spec j hz
  · exact decide_eq_true ⟨hj, hz⟩

/-- The short-list minimum depends only on the coefficient function. -/
theorem canonicalAnchor_congr (r q : Nat) (hq : 1 < q)
    (spec spec' : List (Nat × Nat))
    (hcoef : ∀ j, coefficient q spec j = coefficient q spec' j) :
    canonicalAnchor r q spec = canonicalAnchor r q spec' := by
  have hle : canonicalAnchor r q spec ≤ canonicalAnchor r q spec' := by
    by_cases hlt : canonicalAnchor r q spec' < r
    · apply canonicalAnchor_le_zero r q hq spec _ hlt
      rw [hcoef]
      exact canonicalAnchor_valid r q spec' hlt
    · have heq : canonicalAnchor r q spec' = r := by
        have hbound := canonicalAnchor_le r q spec'
        omega
      rw [heq]
      exact canonicalAnchor_le r q spec
  have hge : canonicalAnchor r q spec' ≤ canonicalAnchor r q spec := by
    by_cases hlt : canonicalAnchor r q spec < r
    · apply canonicalAnchor_le_zero r q hq spec' _ hlt
      rw [← hcoef]
      exact canonicalAnchor_valid r q spec hlt
    · have heq : canonicalAnchor r q spec = r := by
        have hbound := canonicalAnchor_le r q spec
        omega
      rw [heq]
      exact canonicalAnchor_le r q spec'
  omega

theorem range_find_min (r : Nat) (P : Nat → Bool) (a : Nat)
    (ha : (List.range r).find? P = some a) :
    ∀ j < r, P j = true → a ≤ j := by
  intro j _ hj
  by_cases h : a ≤ j
  · exact h
  · have hnot := (List.find?_range_eq_some.mp ha).2.2 j (by omega)
    simp [hj] at hnot

/-- The short candidate scan returns precisely the old increasing-range scan. -/
theorem canonicalAnchor_find (r q : Nat) (hq : 1 < q)
    (spec : List (Nat × Nat)) :
    (List.range r).find? (fun j => decide (coefficient q spec j % q = 0)) =
      if canonicalAnchor r q spec < r then some (canonicalAnchor r q spec) else none := by
  cases hf : (List.range r).find?
      (fun j => decide (coefficient q spec j % q = 0)) with
  | none =>
      have hnot : ¬ canonicalAnchor r q spec < r := by
        intro hlt
        have hz := canonicalAnchor_valid r q spec hlt
        have hnone := List.find?_eq_none.mp hf
        exact hnone _ (List.mem_range.mpr hlt) (decide_eq_true hz)
      simp only [hnot, ite_false]
  | some a =>
      have ha : a < r := List.mem_range.mp (List.mem_of_find?_eq_some hf)
      have hz : coefficient q spec a % q = 0 :=
        of_decide_eq_true (List.find?_some
          (p := fun j => decide (coefficient q spec j % q = 0)) hf)
      have hma := canonicalAnchor_le_zero r q hq spec a ha hz
      have hm : canonicalAnchor r q spec < r := Nat.lt_of_le_of_lt hma ha
      have ham : a ≤ canonicalAnchor r q spec :=
        range_find_min r (fun j => decide (coefficient q spec j % q = 0)) a hf
          _ hm (decide_eq_true (canonicalAnchor_valid r q spec hm))
      have heq : canonicalAnchor r q spec = a := Nat.le_antisymm hma ham
      simp only [heq, ha, ite_true]

def fastAnchorPrefix (r q : Nat) (spec : List (Nat × Nat)) : Bool :=
  let a := canonicalAnchor r q spec
  if a < r then
    walkOK q (fun j => coefficient q spec (j % r)) r (a + 1)
      (nextResidue q 0 0)
  else true

/-- Exact equality, not only soundness: the selected anchor is unchanged. -/
theorem fastAnchorPrefix_eq (r q : Nat) (hq : 1 < q)
    (spec : List (Nat × Nat)) :
    fastAnchorPrefix r q spec = anchorPrefix r q spec := by
  unfold fastAnchorPrefix anchorPrefix
  rw [canonicalAnchor_find r q hq spec]
  by_cases h : canonicalAnchor r q spec < r
  · simp only [h, ite_true]
  · simp only [h, ite_false]

def fastPrefix (r q : Nat) (spec : List (Nat × Nat)) : Bool :=
  if q = 3 then fastAnchorPrefix r q spec
  else if q = 5 then closedPrefix r q spec
  else true

/-- The full prefix remains equal to the previous prefix for every modulus. -/
theorem fastPrefix_eq_legacy (r q : Nat) (spec : List (Nat × Nat)) :
    fastPrefix r q spec = legacyFastPrefix r q spec := by
  unfold fastPrefix legacyFastPrefix
  by_cases hq : q = 3
  · subst q
    simp only [ite_true]
    exact fastAnchorPrefix_eq r 3 (by decide) spec
  · simp only [hq, ite_false]

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
  simp only [positionTest, fastPrefix_eq_legacy, legacyFastPrefix, anchorPrefix, closedPrefix, hcoef]

end A245211New
