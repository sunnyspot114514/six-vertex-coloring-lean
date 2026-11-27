import A245211.Core
import A245211.Cycle

namespace A245211New

open Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem exactSeed_relation (r : Nat) (p d : Nat → Nat)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j) :
    ∀ k ≤ r, 2 ^ k * p k + exactSeed d k =
      (∏ j ∈ range k, d j) * p 0 := by
  intro k
  induction k with
  | zero => simp [exactSeed]
  | succ k ih =>
      intro hk
      calc
        2 ^ (k + 1) * p (k + 1) + exactSeed d (k + 1) =
            2 ^ k * (2 * p (k + 1) + 1) + d k * exactSeed d k := by
              simp only [exactSeed, pow_succ]
              ring
        _ = d k * (2 ^ k * p k + exactSeed d k) := by
              rw [hrec k (by omega)]
              ring
        _ = (∏ j ∈ range (k + 1), d j) * p 0 := by
              rw [ih (by omega), prod_range_succ]
              ring

theorem exactSeed_closed (r : Nat) (p d : Nat → Nat)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hclose : p r = p 0)
    (hprod : (∏ j ∈ range r, d j) = 2 ^ r + 1) :
    exactSeed d r = p 0 := by
  have h := exactSeed_relation r p d hrec r le_rfl
  rw [hclose, hprod] at h
  nlinarith only [h]

theorem seedStep_correct (r q : Nat) (hq : 1 < q) (c d : Nat → Nat)
    (hc : ∀ j < r, c j % q = d j % q) :
    ∀ k ≤ r, seedStep q c k = (exactSeed d k % q, 2 ^ k % q) := by
  intro k
  induction k with
  | zero => simp [seedStep, exactSeed, Nat.mod_eq_of_lt hq]
  | succ k ih =>
      intro hk
      rw [seedStep, ih (by omega)]
      apply Prod.ext
      · simp only [exactSeed, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
        rw [hc k (by omega)]
      · simp [pow_succ, Nat.mul_mod, Nat.mul_comm]

theorem nextResidue_correct (q d x y : Nat) (hq : 1 < q) (hodd : Odd q)
    (hrec : 2 * y + 1 = d * x) :
    nextResidue q (d % q) (x % q) = y % q := by
  have hinv : 2 * ((q + 1) / 2) = q + 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hsum : d * x + (q - 1) = 2 * y + q := by omega
  calc
    nextResidue q (d % q) (x % q) =
        ((d * x + (q - 1)) * ((q + 1) / 2)) % q := by
          simp [nextResidue, Nat.add_mod, Nat.mul_mod]
    _ = ((2 * y + q) * ((q + 1) / 2)) % q := by rw [hsum]
    _ = ((2 * ((q + 1) / 2)) * y + q * ((q + 1) / 2)) % q := by
          congr 1
          ring
    _ = y % q := by
          rw [hinv]
          simp [Nat.add_mul, Nat.add_mod, Nat.mul_mod]

theorem walkOK_correct (r q : Nat) (hq : 1 < q) (hodd : Odd q)
    (p c d : Nat → Nat)
    (hc : ∀ j < r, c j % q = d j % q)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hcop : ∀ j < r, Nat.Coprime (p j) q) :
    ∀ fuel j, j + fuel ≤ r → walkOK q c fuel j (p j % q) = true := by
  intro fuel
  induction fuel with
  | zero => simp [walkOK]
  | succ fuel ih =>
      intro j hj
      have hlt : j < r := by omega
      have hunit : decide (Nat.Coprime (p j % q) q) = true :=
        decide_eq_true ((ZMod.coprime_mod_iff_coprime (p j) q).mpr (hcop j hlt))
      have hnext : nextResidue q (c j) (p j % q) = p (j + 1) % q := by
        calc
          nextResidue q (c j) (p j % q) = nextResidue q (d j % q) (p j % q) := by
            simp only [nextResidue, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
            rw [hc j hlt]
          _ = p (j + 1) % q := nextResidue_correct q _ _ _ hq hodd (hrec j hlt)
      rw [walkOK]
      simp only [hunit, Bool.true_and, hnext]
      exact ih (j + 1) (by omega)

/-- The same cyclic recurrence also closes the checked modular walk. -/
theorem closedWalk_correct (r q : Nat) (hq : 1 < q) (hodd : Odd q)
    (p c d : Nat → Nat)
    (hc : ∀ j < r, c j % q = d j % q)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hclose : p r = p 0)
    (hcop : ∀ j < r, Nat.Coprime (p j) q) :
    ∀ fuel j, j + fuel = r →
      closedWalk q c fuel j (p j % q) (p 0 % q) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro j hj
      have hjeq : j = r := by omega
      subst j
      simp [closedWalk, hclose]
  | succ fuel ih =>
      intro j hj
      have hlt : j < r := by omega
      have hunit : decide (Nat.Coprime (p j % q) q) = true := by
        apply decide_eq_true
        change Nat.gcd (p j % q) q = 1
        rw [← Nat.gcd_rec q (p j), Nat.gcd_comm q (p j)]
        exact hcop j hlt
      have hnext : nextResidue q (c j) (p j % q) = p (j + 1) % q := by
        calc
          nextResidue q (c j) (p j % q) = nextResidue q (d j % q) (p j % q) := by
            simp only [nextResidue, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
            rw [hc j hlt]
          _ = p (j + 1) % q := nextResidue_correct q _ _ _ hq hodd (hrec j hlt)
      rw [closedWalk]
      simp only [hunit, Bool.true_and, hnext]
      exact ih (j + 1) (by omega)

theorem closedPrefix_of_nat_cycle (r q : Nat) (hq : 1 < q) (hodd : Odd q)
    (spec : List (Nat × Nat)) (p d : Nat → Nat)
    (hc : ∀ j < r, coefficient q spec j % q = d j % q)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hclose : p r = p 0)
    (hcop : ∀ j < r, Nat.Coprime (p j) q) :
    closedPrefix r q spec = true := by
  unfold closedPrefix
  apply List.any_eq_true.mpr
  refine ⟨p 0 % q, List.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
  exact closedWalk_correct r q hq hodd p _ d hc hrec hclose hcop r 0 (by omega)

/-- The original value at the last endpoint agrees with the cyclic extension. -/
theorem nat_cycle_value_mod (r : Nat) (_hr : 0 < r) (p : Nat → Nat)
    (hclose : p r = p 0) (k : Nat) (hk : k ≤ r) :
    p (k % r) = p k := by
  by_cases hlt : k < r
  · rw [Nat.mod_eq_of_lt hlt]
  · have heq : k = r := by omega
    subst k
    simp [hclose]

/-- Extending the finite recurrence periodically makes it valid at every
natural index, including across the original endpoint. -/
theorem nat_cycle_mod_recurrence (r : Nat) (hr : 0 < r) (p d : Nat → Nat)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hclose : p r = p 0) (j : Nat) :
    2 * p ((j + 1) % r) + 1 = d (j % r) * p (j % r) := by
  have hj : j % r < r := Nat.mod_lt j hr
  have hnext : p ((j + 1) % r) = p (j % r + 1) := by
    rw [show (j + 1) % r = (j % r + 1) % r by simp [Nat.add_mod]]
    exact nat_cycle_value_mod r hr p hclose _ (by omega)
  rw [hnext]
  exact hrec (j % r) hj

theorem anchorPrefix_of_nat_cycle (r q : Nat) (hq : 1 < q) (hodd : Odd q)
    (spec : List (Nat × Nat)) (p d : Nat → Nat)
    (hc : ∀ j < r, coefficient q spec j % q = d j % q)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hclose : p r = p 0)
    (hcop : ∀ j < r, Nat.Coprime (p j) q) :
    anchorPrefix r q spec = true := by
  unfold anchorPrefix
  cases hfind : (List.range r).find?
      (fun j => decide (coefficient q spec j % q = 0)) with
  | none => rfl
  | some a =>
      have ha : a < r := List.mem_range.mp (List.mem_of_find?_eq_some hfind)
      have hzero : coefficient q spec a % q = 0 :=
        of_decide_eq_true (List.find?_some
          (p := fun j => decide (coefficient q spec j % q = 0)) hfind)
      have hr : 0 < r := by omega
      have hnext : nextResidue q (coefficient q spec a) (p a % q) =
          p (a + 1) % q := by
        calc
          nextResidue q (coefficient q spec a) (p a % q) =
              nextResidue q (d a % q) (p a % q) := by
                simp only [nextResidue, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
                rw [hc a ha]
          _ = p (a + 1) % q := nextResidue_correct q _ _ _ hq hodd (hrec a ha)
      have hconstant : nextResidue q (coefficient q spec a) (p a % q) =
          nextResidue q 0 0 := by
        simp [nextResidue, Nat.add_mod, Nat.mul_mod, hzero]
      have hanchor : p ((a + 1) % r) % q = nextResidue q 0 0 := by
        rw [nat_cycle_value_mod r hr p hclose (a + 1) (by omega)]
        exact hnext.symm.trans hconstant
      have hw := walkOK_correct (a + 1 + r) q hq hodd
        (fun j => p (j % r))
        (fun j => coefficient q spec (j % r))
        (fun j => d (j % r))
        (fun j _ => hc (j % r) (Nat.mod_lt j hr))
        (fun j _ => nat_cycle_mod_recurrence r hr p d hrec hclose j)
        (fun j _ => hcop (j % r) (Nat.mod_lt j hr))
        r (a + 1) (by omega)
      simpa only [hanchor] using hw

/-- Every genuine prime cycle passes the inexpensive necessary prefix.
This uses no product equation; it follows from the cyclic recurrence alone. -/
theorem fastPrefix_of_nat_cycle (r q : Nat) (hq : 1 < q) (hodd : Odd q)
    (spec : List (Nat × Nat)) (p d : Nat → Nat)
    (hc : ∀ j < r, coefficient q spec j % q = d j % q)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hclose : p r = p 0)
    (hcop : ∀ j < r, Nat.Coprime (p j) q) :
    fastPrefix r q spec = true := by
  unfold fastPrefix
  split
  · exact anchorPrefix_of_nat_cycle r q hq hodd spec p d hc hrec hclose hcop
  · split
    · exact closedPrefix_of_nat_cycle r q hq hodd spec p d hc hrec hclose hcop
    · rfl

theorem positionTest_of_nat_cycle (r q : Nat) (hq : 1 < q) (hodd : Odd q)
    (spec : List (Nat × Nat)) (p d : Nat → Nat)
    (hc : ∀ j < r, coefficient q spec j % q = d j % q)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hclose : p r = p 0)
    (hprod : (∏ j ∈ range r, d j) = 2 ^ r + 1)
    (hcop : ∀ j < r, Nat.Coprime (p j) q) :
    positionTest r q spec = true := by
  unfold positionTest
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact fastPrefix_of_nat_cycle r q hq hodd spec p d hc hrec hclose hcop
  · rw [seedStep_correct r q hq _ d hc r le_rfl]
    rw [exactSeed_closed r p d hrec hclose hprod]
    exact walkOK_correct r q hq hodd p _ d hc hrec hcop r 0 (by omega)

def cyclicValue {r : Nat} (hr : 0 < r) (f : Fin r → Nat) (j : Nat) : Nat :=
  f ⟨j % r, Nat.mod_lt j hr⟩

theorem cyclicValue_at {r : Nat} (hr : 0 < r) (f : Fin r → Nat) (i : Fin r) :
    cyclicValue hr f i.val = f i := by
  simp [cyclicValue, Nat.mod_eq_of_lt i.isLt]

theorem positionTest_of_cycle {r : Nat} (hr : 0 < r)
    (q : Nat) (hq : 1 < q) (hodd : Odd q)
    (spec : List (Nat × Nat)) (p d : Fin r → Nat)
    (hc : ∀ i : Fin r, coefficient q spec i.val % q = d i % q)
    (hrec : ∀ i, 2 * p (cycleNext i) + 1 = d i * p i)
    (hprod : (∏ i, d i) = 2 ^ r + 1)
    (hp : ∀ i, (p i).Prime) (hlarge : ∀ i, q < p i) :
    positionTest r q spec = true := by
  apply positionTest_of_nat_cycle r q hq hodd spec
    (cyclicValue hr p) (cyclicValue hr d)
  · intro j hj
    simpa [cyclicValue, Nat.mod_eq_of_lt hj] using hc ⟨j, hj⟩
  · intro j hj
    have hnext : cycleNext (⟨j, hj⟩ : Fin r) =
        ⟨(j + 1) % r, Nat.mod_lt _ hr⟩ := rfl
    simpa [cyclicValue, Nat.mod_eq_of_lt hj, hnext] using hrec ⟨j, hj⟩
  · simp [cyclicValue]
  · calc
      (∏ j ∈ range r, cyclicValue hr d j) = ∏ i : Fin r, cyclicValue hr d i.val :=
        (Fin.prod_univ_eq_prod_range (cyclicValue hr d) r).symm
      _ = ∏ i, d i := prod_congr rfl fun i _ => cyclicValue_at hr d i
      _ = 2 ^ r + 1 := hprod
  · intro j hj
    have hi := hp ⟨j, hj⟩
    have hl := hlarge ⟨j, hj⟩
    simpa [cyclicValue, Nat.mod_eq_of_lt hj] using
      hi.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hl)

end A245211New
