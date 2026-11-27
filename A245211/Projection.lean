import A245211.Checker
import A245211.TokenAllocation
import Mathlib.Data.List.OfFn

/-!
# Passing prime-token allocations to the modular checker

The checker accepts a list of `(prime token, position)` pairs.  These lemmas
connect that representation to the integer multipliers, and justify deleting
every token whose residue is one.  All deletion lemmas hold simultaneously
for every position; no enumeration of position equalities is needed.
-/

namespace A245211New

open Finset

/-- Multiplying the position multipliers counts every token exactly once. -/
theorem prod_tokenMultiplier {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : List ℕ) (pos : Fin L.length → ι) :
    (∏ i, tokenMultiplier L pos i) = L.prod := by
  classical
  unfold tokenMultiplier
  rw [prod_comm]
  simp

/-- The checker's list representation, with the value before the position. -/
def tokenSpec {r : ℕ} (L : List ℕ) (pos : Fin L.length → Fin r) :
    List (ℕ × ℕ) :=
  List.ofFn fun j => (L[j], (pos j).val)

@[simp] theorem coefficient_nil (q j : ℕ) : coefficient q [] j = 1 := rfl

@[simp] theorem coefficient_cons (q : ℕ) (tp : ℕ × ℕ)
    (spec : List (ℕ × ℕ)) (j : ℕ) :
    coefficient q (tp :: spec) j =
      if tp.2 = j then (tp.1 % q * coefficient q spec j) % q
      else coefficient q spec j := rfl

/-- The modular fold computes the residue of the selected ordinary product. -/
theorem coefficient_eq_map_prod_mod (q : ℕ) (hq : 1 < q)
    (spec : List (ℕ × ℕ)) (j : ℕ) :
    coefficient q spec j =
      (spec.map (fun tp => if tp.2 = j then tp.1 else 1)).prod % q := by
  induction spec with
  | nil => simp [Nat.mod_eq_of_lt hq]
  | cons tp spec ih =>
      rw [coefficient_cons, List.map_cons, List.prod_cons, ih]
      by_cases hpos : tp.2 = j <;> simp [hpos, Nat.mul_mod]

/-- The coefficient is already reduced when the modulus exceeds one. -/
@[simp] theorem coefficient_mod (q : ℕ) (hq : 1 < q)
    (spec : List (ℕ × ℕ)) (j : ℕ) :
    coefficient q spec j % q = coefficient q spec j := by
  simp only [coefficient_eq_map_prod_mod q hq spec j, Nat.mod_mod]

/-- An allocated token specification yields exactly the multiplier residue. -/
theorem coefficient_tokenSpec {r : ℕ} (q : ℕ) (hq : 1 < q)
    (L : List ℕ) (pos : Fin L.length → Fin r) (i : Fin r) :
    coefficient q (tokenSpec L pos) i.val = tokenMultiplier L pos i % q := by
  rw [coefficient_eq_map_prod_mod q hq]
  simp [tokenSpec, tokenMultiplier, List.map_ofFn, Fin.prod_ofFn, Fin.val_eq_val]

theorem coefficient_tokenSpec_mod {r : ℕ} (q : ℕ) (hq : 1 < q)
    (L : List ℕ) (pos : Fin L.length → Fin r) (i : Fin r) :
    coefficient q (tokenSpec L pos) i.val % q = tokenMultiplier L pos i % q := by
  rw [coefficient_mod q hq, coefficient_tokenSpec q hq]

/-- A token with residue one can be deleted, regardless of its position. -/
theorem coefficient_cons_mod_one (q : ℕ) (hq : 1 < q)
    (tp : ℕ × ℕ) (spec : List (ℕ × ℕ)) (j : ℕ)
    (htp : tp.1 % q = 1) :
    coefficient q (tp :: spec) j = coefficient q spec j := by
  rw [coefficient_cons, htp]
  simp [coefficient_mod q hq]

/-- A neutral token may also be removed from the middle of a specification. -/
theorem coefficient_append_mod_one (q : ℕ) (hq : 1 < q)
    (before after : List (ℕ × ℕ)) (tp : ℕ × ℕ) (j : ℕ)
    (htp : tp.1 % q = 1) :
    coefficient q (before ++ tp :: after) j =
      coefficient q (before ++ after) j := by
  induction before with
  | nil => exact coefficient_cons_mod_one q hq tp after j htp
  | cons head before ih =>
      simp only [List.cons_append, coefficient_cons, ih]

/-- Reducing each token value before building the specification changes
neither its positions nor the resulting coefficient. -/
theorem coefficient_map_mod (q : ℕ) (spec : List (ℕ × ℕ)) (j : ℕ) :
    coefficient q (spec.map (fun tp => (tp.1 % q, tp.2))) j =
      coefficient q spec j := by
  induction spec with
  | nil => rfl
  | cons tp spec ih =>
      simp only [List.map_cons, coefficient_cons, Nat.mod_mod, ih]

/-- All neutral tokens can be filtered out in one step. -/
theorem coefficient_filter_ne_one (q : ℕ) (hq : 1 < q)
    (spec : List (ℕ × ℕ)) (j : ℕ) :
    coefficient q (spec.filter (fun tp => decide (tp.1 % q ≠ 1))) j =
      coefficient q spec j := by
  induction spec with
  | nil => rfl
  | cons tp spec ih =>
      by_cases htp : tp.1 % q = 1 <;>
        simp [List.filter_cons, htp, coefficient_cons, ih, coefficient_mod q hq]

/-- The reduced list used by a modular certificate.  Its entries retain their
original values; the checker's coefficient function reduces those values. -/
def projectedTokenSpec {r : ℕ} (q : ℕ) (L : List ℕ)
    (pos : Fin L.length → Fin r) : List (ℕ × ℕ) :=
  (tokenSpec L pos).filter fun tp => decide (tp.1 % q ≠ 1)

theorem coefficient_projectedTokenSpec {r : ℕ} (q : ℕ) (hq : 1 < q)
    (L : List ℕ) (pos : Fin L.length → Fin r) (i : Fin r) :
    coefficient q (projectedTokenSpec q L pos) i.val =
      tokenMultiplier L pos i % q := by
  unfold projectedTokenSpec
  rw [coefficient_filter_ne_one q hq, coefficient_tokenSpec q hq]

/-- Specifications with the same coefficient function give the same test. -/
theorem positionTest_congr (r q : ℕ) (spec spec' : List (ℕ × ℕ))
    (h : ∀ j, coefficient q spec j = coefficient q spec' j) :
    positionTest r q spec = positionTest r q spec' := by
  have hfun : coefficient q spec = coefficient q spec' := funext h
  simp only [positionTest, hfun]

theorem positionTest_filter_ne_one (r q : ℕ) (hq : 1 < q)
    (spec : List (ℕ × ℕ)) :
    positionTest r q (spec.filter (fun tp => decide (tp.1 % q ≠ 1))) =
      positionTest r q spec := by
  apply positionTest_congr
  intro j
  exact coefficient_filter_ne_one q hq spec j

theorem positionTest_append_mod_one (r q : ℕ) (hq : 1 < q)
    (before after : List (ℕ × ℕ)) (tp : ℕ × ℕ) (htp : tp.1 % q = 1) :
    positionTest r q (before ++ tp :: after) =
      positionTest r q (before ++ after) := by
  apply positionTest_congr
  intro j
  exact coefficient_append_mod_one q hq before after tp j htp

/-- A real prime-token cycle passes the checker's full specification. -/
theorem positionTest_of_token_cycle {r : ℕ} (hr : 0 < r)
    (q : ℕ) (hq : 1 < q) (hodd : Odd q)
    (L : List ℕ) (pos : Fin L.length → Fin r) (p : Fin r → ℕ)
    (hfactor : L.prod = 2 ^ r + 1)
    (hrec : ∀ i, 2 * p (cycleNext i) + 1 = tokenMultiplier L pos i * p i)
    (hp : ∀ i, (p i).Prime) (hlarge : ∀ i, q < p i) :
    positionTest r q (tokenSpec L pos) = true := by
  apply positionTest_of_cycle hr q hq hodd (tokenSpec L pos) p (tokenMultiplier L pos)
  · exact coefficient_tokenSpec_mod q hq L pos
  · exact hrec
  · exact (prod_tokenMultiplier L pos).trans hfactor
  · exact hp
  · exact hlarge

/-- A real prime-token cycle also passes the shorter projected specification. -/
theorem positionTest_of_projected_token_cycle {r : ℕ} (hr : 0 < r)
    (q : ℕ) (hq : 1 < q) (hodd : Odd q)
    (L : List ℕ) (pos : Fin L.length → Fin r) (p : Fin r → ℕ)
    (hfactor : L.prod = 2 ^ r + 1)
    (hrec : ∀ i, 2 * p (cycleNext i) + 1 = tokenMultiplier L pos i * p i)
    (hp : ∀ i, (p i).Prime) (hlarge : ∀ i, q < p i) :
    positionTest r q (projectedTokenSpec q L pos) = true := by
  unfold projectedTokenSpec
  rw [positionTest_filter_ne_one r q hq]
  exact positionTest_of_token_cycle hr q hq hodd L pos p hfactor hrec hp hlarge

end A245211New
