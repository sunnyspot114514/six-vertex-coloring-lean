import OMAReductions.R_OeisA245211_conjecture_R2_H3_R1
import Mathlib
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

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

/-!
# Cyclic prime equations for squarefree fixed points of A245211

The product equation and the lower bound on its primes are public lemmas of
the upstream reduction.  The closed-subset argument below explains why a
prime-divisibility map must consist of one cycle.  This mathematical route is
also used in the upstream proof of the prime-power-count case (R2.H1).
-/

namespace A245211New

open Finset Function
open OMA.R_OeisA245211_conjecture_R2
  (baseProduct_lt large_prime squarefree_fixed_point_product)

/-- Successor on a finite cycle, defined also for the empty domain. -/
def cycleNext {r : ℕ} (i : Fin r) : Fin r :=
  ⟨(i.val + 1) % r, Nat.mod_lt _ (by have hi := i.isLt; omega)⟩

section FiniteProducts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- No nonempty proper subset can be closed under a prime-divisibility map:
its integer product quotient is already too large. -/
private theorem closed_subset_is_all (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hi : Injective p)
    (hbalance : (∏ i, (2 * p i + 1)) =
      (2 ^ Fintype.card ι + 1) * ∏ i, p i)
    (f : ι → ι) (hf : ∀ i, p i ∣ 2 * p (f i) + 1)
    (S : Finset ι) (hS : S.Nonempty) (hclosed : ∀ i ∈ S, f i ∈ S) :
    S = univ := by
  have hdiv : (∏ i ∈ S, p i) ∣ ∏ i ∈ S, (2 * p i + 1) := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro i _ j _ hij
      apply Nat.coprime_iff_isRelPrime.mp
      exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hi h))
    · intro i him
      exact (hf i).trans (dvd_prod_of_mem _ (hclosed i him))
  obtain ⟨k, hk⟩ := hdiv
  have hSpos : 0 < ∏ i ∈ S, p i := prod_pos fun i _ => (hp i).pos
  have hkmin : 2 ^ S.card + 1 ≤ k := by
    have hstrict := baseProduct_lt p S hS hp
    rw [hk, mul_comm (∏ i ∈ S, p i) k] at hstrict
    exact Nat.succ_le_of_lt ((Nat.mul_lt_mul_right hSpos).mp hstrict)

  let T : Finset ι := univ \ S
  have hdisj : Disjoint T S := disjoint_sdiff_self_left
  have hcover : T ∪ S = univ := sdiff_union_of_subset (subset_univ S)
  have hcard : Fintype.card ι = T.card + S.card := by
    rw [← card_union_of_disjoint hdisj, hcover, card_univ]
  have hremaining : k * (∏ i ∈ T, (2 * p i + 1)) =
      (2 ^ Fintype.card ι + 1) * ∏ i ∈ T, p i := by
    have htotal := hbalance
    rw [← hcover, prod_union hdisj, prod_union hdisj, hk] at htotal
    apply Nat.eq_of_mul_eq_mul_right hSpos
    nlinarith only [htotal]
  by_contra hproper
  have hT : T.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro hempty
    apply hproper
    simpa only [hempty, empty_union] using hcover
  have hTpos : 0 < ∏ i ∈ T, p i := prod_pos fun i _ => (hp i).pos
  have hTbound : 2 ^ T.card * (∏ i ∈ T, p i) ≤
      ∏ i ∈ T, (2 * p i + 1) := by
    rw [← prod_const, ← prod_mul_distrib]
    exact prod_le_prod' fun _ _ => Nat.le_succ _
  have hineq := Nat.mul_le_mul hkmin hTbound
  rw [hremaining, hcard, pow_add, ← mul_assoc] at hineq
  have hcancel : (2 ^ S.card + 1) * 2 ^ T.card ≤
      2 ^ T.card * 2 ^ S.card + 1 := le_of_mul_le_mul_right hineq hTpos
  have htwo : 2 ≤ 2 ^ T.card := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (card_pos.mpr hT)
  rw [add_mul, one_mul, mul_comm (2 ^ S.card)] at hcancel
  omega

/-- A finite function with no nonempty proper closed subset has an enumeration
in which it is exactly cyclic successor. -/
private theorem enumerate_cycle [Nonempty ι] (f : ι → ι)
    (hfull : ∀ S : Finset ι, S.Nonempty →
      (∀ i ∈ S, f i ∈ S) → S = univ) :
    Bijective f ∧ ∃ e : Fin (Fintype.card ι) ≃ ι,
      ∀ i, e (cycleNext i) = f (e i) := by
  have hsurj : Surjective f := by
    have himage : univ.image f = univ := by
      apply hfull _ (univ_nonempty.image f)
      intro i _
      exact mem_image.mpr ⟨i, mem_univ i, rfl⟩
    intro y
    have hy : y ∈ univ.image f := by rw [himage]; exact mem_univ y
    obtain ⟨x, _, hxy⟩ := mem_image.mp hy
    exact ⟨x, hxy⟩
  have hinj : Injective f := Finite.injective_iff_surjective.mpr hsurj
  classical
  let x : ι := Classical.choice inferInstance
  let period : ℕ := minimalPeriod f x
  have hperiodpos : 0 < period :=
    minimalPeriod_pos_of_mem_periodicPts (hinj.mem_periodicPts x)
  let orbit : Finset ι := (range period).image (fun j => f^[j] x)
  have horbit : orbit = univ := by
    apply hfull
    · exact ⟨x, mem_image.mpr ⟨0, mem_range.mpr hperiodpos, rfl⟩⟩
    · intro y hy
      obtain ⟨j, _, rfl⟩ := mem_image.mp hy
      refine mem_image.mpr ⟨(j + 1) % period,
        mem_range.mpr (Nat.mod_lt _ hperiodpos), ?_⟩
      dsimp only [period]
      rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply']
  have horbitcard : orbit.card = period := by
    dsimp only [orbit]
    rw [card_image_of_injOn, card_range]
    intro i hi j hj hij
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod
      (mem_range.mp hi) (mem_range.mp hj)).mp hij
  have hperiod : minimalPeriod f x = Fintype.card ι := by
    rw [horbit, card_univ] at horbitcard
    exact horbitcard.symm
  let enumerate : Fin (Fintype.card ι) → ι := fun i => f^[i.val] x
  have heinj : Injective enumerate := by
    intro i j hij
    apply Fin.ext
    exact (iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by rw [hperiod]; exact i.isLt)
      (by rw [hperiod]; exact j.isLt)).mp hij
  have hesurj : Surjective enumerate := by
    intro y
    have hy : y ∈ orbit := by rw [horbit]; exact mem_univ y
    obtain ⟨j, hj, hjy⟩ := mem_image.mp hy
    refine ⟨⟨j, ?_⟩, hjy⟩
    have hjlt : j < minimalPeriod f x := mem_range.mp hj
    rwa [hperiod] at hjlt
  refine ⟨⟨hinj, hsurj⟩, Equiv.ofBijective enumerate ⟨heinj, hesurj⟩, ?_⟩
  intro i
  change f^[((i.val + 1) % Fintype.card ι)] x = f (f^[i.val] x)
  have hindex : (i.val + 1) % Fintype.card ι =
      (i.val + 1) % minimalPeriod f x :=
    congrArg (fun k : ℕ => (i.val + 1) % k) hperiod.symm
  rw [hindex, iterate_mod_minimalPeriod_eq, iterate_succ_apply']

private theorem prime_product_cycle [Nonempty ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hi : Injective p)
    (hsize : 2 ≤ Fintype.card ι)
    (hbalance : (∏ i, (2 * p i + 1)) =
      (2 ^ Fintype.card ι + 1) * ∏ i, p i) :
    ∃ P d : Fin (Fintype.card ι) → ℕ,
      (∀ i, (P i).Prime ∧ 2 ^ (Fintype.card ι - 1) < P i) ∧
      (∀ i, 2 * P (cycleNext i) + 1 = d i * P i) ∧
      (∏ i, d i) = 2 ^ Fintype.card ι + 1 := by
  classical
  have hfactor (i : ι) : ∃ j, p i ∣ 2 * p j + 1 := by
    have hdiv : p i ∣ ∏ j, (2 * p j + 1) := by
      rw [hbalance]
      exact dvd_mul_of_dvd_right (dvd_prod_of_mem p (mem_univ i)) _
    obtain ⟨j, _, hj⟩ := ((hp i).prime.dvd_finsetProd_iff
      (fun j => 2 * p j + 1)).mp hdiv
    exact ⟨j, hj⟩
  choose f hf using hfactor
  obtain ⟨hbij, e, he⟩ := enumerate_cycle f
    (closed_subset_is_all p hp hi hbalance f hf)
  choose coefficient hc using hf
  have hcoeff : (∏ i, coefficient i) = 2 ^ Fintype.card ι + 1 := by
    apply Nat.eq_of_mul_eq_mul_left
      (show 0 < ∏ i, p i from prod_pos fun i _ => (hp i).pos)
    calc
      (∏ i, p i) * (∏ i, coefficient i) = ∏ i, (2 * p (f i) + 1) := by
        rw [← prod_mul_distrib]
        exact prod_congr rfl fun i _ => (hc i).symm
      _ = ∏ i, (2 * p i + 1) :=
        Fintype.prod_equiv (Equiv.ofBijective f hbij) _ _ (fun _ => rfl)
      _ = (∏ i, p i) * (2 ^ Fintype.card ι + 1) := by rw [hbalance]; ring
  refine ⟨fun i => p (e i), fun i => coefficient (e i), ?_, ?_, ?_⟩
  · intro i
    exact ⟨hp _, large_prime p hp hsize hbalance _⟩
  · intro i
    change 2 * p (e (cycleNext i)) + 1 = coefficient (e i) * p (e i)
    rw [he i, hc (e i), mul_comm]
  · calc
      (∏ i, coefficient (e i)) = ∏ i, coefficient i :=
        Fintype.prod_equiv e _ _ (fun _ => rfl)
      _ = 2 ^ Fintype.card ι + 1 := hcoeff

end FiniteProducts

/-- Every squarefree fixed point with at least three distinct prime factors
produces one complete cycle of large primes with the prescribed multiplier
product.  The recurrence has a unique next residue modulo every odd modulus. -/
theorem squarefree_cycle {n r : ℕ} (hs : Squarefree n)
    (ha : OeisA245211.a n = n) (hr : n.primeFactors.card = r) (hr3 : 3 ≤ r) :
    ∃ p d : Fin r → ℕ,
      (∀ i, (p i).Prime ∧ 2 ^ (r - 1) < p i) ∧
      (∀ i, 2 * p (cycleNext i) + 1 = d i * p i) ∧
      (∏ i, d i) = 2 ^ r + 1 := by
  classical
  let S := n.primeFactors
  have hcard : Fintype.card S = r := by simpa [S] using hr
  have hnonempty : S.Nonempty := card_pos.mp (by dsimp [S]; omega)
  letI : Nonempty S := hnonempty.to_subtype
  have hbalance : (∏ i : S, (2 * (i : ℕ) + 1)) =
      (2 ^ Fintype.card S + 1) * ∏ i : S, (i : ℕ) := by
    calc
      (∏ i : S, (2 * (i : ℕ) + 1)) = ∏ p ∈ S, (2 * p + 1) :=
        prod_coe_sort S (fun p => 2 * p + 1)
      _ = (2 ^ S.card + 1) * ∏ p ∈ S, p := squarefree_fixed_point_product hs ha
      _ = (2 ^ Fintype.card S + 1) * ∏ i : S, (i : ℕ) := by
        rw [Fintype.card_coe]
        exact congrArg (fun v : ℕ => (2 ^ S.card + 1) * v)
          (prod_coe_sort S (fun p => p)).symm
  have hcycle := prime_product_cycle (fun i : S => (i : ℕ))
    (fun i => Nat.prime_of_mem_primeFactors i.property) Subtype.val_injective
    (by omega) hbalance
  cases hcard
  exact hcycle

end A245211New

/-!
# Allocating prime occurrences to the multipliers of a cycle

The indices of a factor list distinguish repeated prime factors.  Thus a list
such as `[3, 3, 11]` has three tokens, even though two tokens have the same
value.  The allocation theorem below uses only primality and equality of the
two products.  It does not make a squarefreeness assumption about that product.
-/

namespace A245211New

open Finset

/-- The product of all prime tokens assigned to one position. -/
def tokenMultiplier {ι : Type*} [DecidableEq ι] (L : List ℕ)
    (pos : Fin L.length → ι) (i : ι) : ℕ :=
  ∏ j : Fin L.length, if pos j = i then L[j] else 1

/-- Every factorization of a finite product of prime occurrences allocates
each occurrence to exactly one factor.  Repeated primes remain distinct
because the allocation is indexed by positions in the list. -/
theorem allocate_prime_tokens {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : List ℕ) (hL : ∀ q ∈ L, Nat.Prime q)
    (d : ι → ℕ) (hprod : (∏ i, d i) = L.prod) :
    ∃ pos : Fin L.length → ι, ∀ i, d i = tokenMultiplier L pos i := by
  classical
  revert hprod
  revert d
  revert hL
  induction L with
  | nil =>
      intro hL d hprod
      refine ⟨Fin.elim0, ?_⟩
      intro i
      have hdiv : d i ∣ 1 := by
        simpa only [hprod, List.prod_nil] using
          (dvd_prod_of_mem d (mem_univ i))
      simpa [tokenMultiplier] using hdiv
  | cons q L ih =>
      intro hL d hprod
      have hq : q.Prime := hL q (by simp)
      have htailprime : ∀ t ∈ L, t.Prime := by
        intro t ht
        exact hL t (by simp [ht])
      have hqdiv : q ∣ ∏ i, d i := by
        rw [hprod, List.prod_cons]
        exact dvd_mul_right q L.prod
      obtain ⟨a, _, ha⟩ := (hq.prime.dvd_finsetProd_iff d).mp hqdiv
      obtain ⟨c, hc⟩ := ha
      let rest : ι → ℕ := fun i => if a = i then c else d i
      have hpoint (i : ι) : d i = (if a = i then q else 1) * rest i := by
        by_cases hai : a = i
        · subst i
          simpa [rest] using hc
        · simp [rest, hai]
      have hsplit : (∏ i, d i) = q * ∏ i, rest i := by
        calc
          (∏ i, d i) = ∏ i, ((if a = i then q else 1) * rest i) :=
            prod_congr rfl fun i _ => hpoint i
          _ = (∏ i : ι, if a = i then q else 1) * ∏ i, rest i :=
            prod_mul_distrib
          _ = q * ∏ i, rest i := by simp
      have hrest : (∏ i, rest i) = L.prod := by
        apply Nat.eq_of_mul_eq_mul_left hq.pos
        rw [← hsplit, hprod, List.prod_cons]
      obtain ⟨pos, hpos⟩ := ih htailprime rest hrest
      refine ⟨Fin.cons a pos, ?_⟩
      intro i
      rw [hpoint i, hpos i]
      simp [tokenMultiplier, Fin.prod_univ_succ]

/-- The explicit modular successor agrees with addition in `Fin r`. -/
theorem cycleNext_eq_add_one {r : ℕ} [NeZero r] (i : Fin r) :
    cycleNext i = i + 1 := by
  apply Fin.ext
  simp [cycleNext, Fin.val_add, Fin.val_one', Nat.add_mod]

/-- Moving the origin of a finite cycle commutes with cyclic successor. -/
theorem cycleNext_add {r : ℕ} [NeZero r] (i s : Fin r) :
    cycleNext i + s = cycleNext (i + s) := by
  simp only [cycleNext_eq_add_one]
  abel

/-- Translate all cycle positions so that a chosen prime token is at zero.
The bound on each prime and the exact integer recurrence are preserved. -/
theorem normalize_token_cycle {r : ℕ} [NeZero r]
    (L : List ℕ) (pos : Fin L.length → Fin r)
    (p : Fin r → ℕ) (j₀ : Fin L.length)
    (hp : ∀ i, (p i).Prime ∧ 2 ^ (r - 1) < p i)
    (hcycle : ∀ i, 2 * p (cycleNext i) + 1 =
      tokenMultiplier L pos i * p i) :
    ∃ pos' : Fin L.length → Fin r, ∃ p' : Fin r → ℕ,
      pos' j₀ = 0 ∧
      (∀ i, (p' i).Prime ∧ 2 ^ (r - 1) < p' i) ∧
      (∀ i, 2 * p' (cycleNext i) + 1 =
        tokenMultiplier L pos' i * p' i) := by
  let s := pos j₀
  refine ⟨fun j => pos j - s, fun i => p (i + s), ?_, ?_, ?_⟩
  · simp [s]
  · intro i
    exact hp (i + s)
  · intro i
    change 2 * p (cycleNext i + s) + 1 =
      tokenMultiplier L (fun j => pos j - s) i * p (i + s)
    rw [cycleNext_add, hcycle]
    congr 1
    unfold tokenMultiplier
    apply prod_congr rfl
    intro j _
    simp only [sub_eq_iff_eq_add]

/-- A squarefree fixed point gives a normalized prime-token cycle whenever
the prescribed multiplier product has been factored into a list of primes. -/
theorem squarefree_token_cycle {n r : ℕ} (hs : Squarefree n)
    (ha : OeisA245211.a n = n) (hr : n.primeFactors.card = r)
    (hr3 : 3 ≤ r) (L : List ℕ) (hL : ∀ q ∈ L, Nat.Prime q)
    (hfactor : L.prod = 2 ^ r + 1) (j₀ : Fin L.length) :
    letI : NeZero r := ⟨by omega⟩
    ∃ pos : Fin L.length → Fin r, ∃ p : Fin r → ℕ,
      pos j₀ = 0 ∧
      (∀ i, (p i).Prime ∧ 2 ^ (r - 1) < p i) ∧
      (∀ i, 2 * p (cycleNext i) + 1 =
        tokenMultiplier L pos i * p i) := by
  letI : NeZero r := ⟨by omega⟩
  obtain ⟨p, d, hp, hcycle, hprod⟩ := squarefree_cycle hs ha hr hr3
  obtain ⟨pos, hpos⟩ := allocate_prime_tokens L hL d (hprod.trans hfactor.symm)
  apply normalize_token_cycle L pos p j₀ hp
  intro i
  rw [← hpos i]
  exact hcycle i

end A245211New

namespace A245211New

open Finset

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem exactSeed_closed (r : Nat) (p d : Nat → Nat)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hclose : p r = p 0)
    (hprod : (∏ j ∈ range r, d j) = 2 ^ r + 1) :
    exactSeed d r = p 0 := by
  have h := exactSeed_relation r p d hrec r le_rfl
  rw [hclose, hprod] at h
  nlinarith only [h]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

/- The same cyclic recurrence also closes the checked modular walk. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

/- The original value at the last endpoint agrees with the cyclic extension. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem nat_cycle_value_mod (r : Nat) (_hr : 0 < r) (p : Nat → Nat)
    (hclose : p r = p 0) (k : Nat) (hk : k ≤ r) :
    p (k % r) = p k := by
  by_cases hlt : k < r
  · rw [Nat.mod_eq_of_lt hlt]
  · have heq : k = r := by omega
    subst k
    simp [hclose]

/- Extending the finite recurrence periodically makes it valid at every
natural index, including across the original endpoint. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

/- Every genuine prime cycle passes the inexpensive necessary prefix.
This uses no product equation; it follows from the cyclic recurrence alone. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem fastPrefix_of_nat_cycle (r q : Nat) (hq : 1 < q) (hodd : Odd q)
    (spec : List (Nat × Nat)) (p d : Nat → Nat)
    (hc : ∀ j < r, coefficient q spec j % q = d j % q)
    (hrec : ∀ j < r, 2 * p (j + 1) + 1 = d j * p j)
    (hclose : p r = p 0)
    (hcop : ∀ j < r, Nat.Coprime (p j) q) :
    fastPrefix r q spec = true := by
  rw [fastPrefix_eq_legacy]
  unfold legacyFastPrefix
  split
  · exact anchorPrefix_of_nat_cycle r q hq hodd spec p d hc hrec hclose hcop
  · split
    · exact closedPrefix_of_nat_cycle r q hq hodd spec p d hc hrec hclose hcop
    · rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem cyclicValue_at {r : Nat} (hr : 0 < r) (f : Fin r → Nat) (i : Fin r) :
    cyclicValue hr f i.val = f i := by
  simp [cyclicValue, Nat.mod_eq_of_lt i.isLt]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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
      simp only [decide_not] at ih
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
  simp only [positionTest, fastPrefix_eq_legacy, legacyFastPrefix, anchorPrefix, closedPrefix, hfun]

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

/-!
# Excluding squarefree fixed points with exactly 65 prime factors

The prime factors of 2^65 + 1 are all congruent to one modulo five,
except for the single factor three. Rotating that token to position zero
leaves one projected specification, independent of every other position.
-/

namespace A245211New

abbrev factors65 : List Nat := [3, 11, 131, 2731, 409891, 7623851]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem count65_rejected :
    positionTest 65 5 [(3, 0)] = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count65 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 65) : OeisA245211.a n ≠ n := by
  intro ha
  have hprime : ∀ q ∈ factors65, Nat.Prime q := by
    norm_num [factors65]
  have hfactor : factors65.prod = 2 ^ 65 + 1 := by
    norm_num [factors65]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide)
      factors65 hprime hfactor (0 : Fin 6)
  have hlarge (i : Fin 65) : 5 < p i := by
    exact lt_trans (by norm_num : 5 < 2 ^ (65 - 1)) (hp i).2
  have hspec : tokenSpec factors65 pos =
      [(3, 0), (11, (pos 1).val), (131, (pos 2).val),
        (2731, (pos 3).val), (409891, (pos 4).val),
        (7623851, (pos 5).val)] := by
    simp [tokenSpec, factors65, List.ofFn_succ, hzero]
  have hfiltered : projectedTokenSpec 5 factors65 pos = [(3, 0)] := by
    change (tokenSpec factors65 pos).filter
      (fun tp => decide (tp.1 % 5 ≠ 1)) = [(3, 0)]
    rw [hspec]
    norm_num [List.filter_cons, List.filter_nil]
  have hh := positionTest_of_projected_token_cycle (by decide)
    5 (by decide) (by decide) factors65 pos p hfactor hrec
      (fun i => (hp i).1) hlarge
  rw [hfiltered, count65_rejected] at hh
  cases hh

theorem squarefree_no_fixed_count65 :
    ∀ n : Nat, Squarefree n → n.primeFactors.card = 65 →
      OeisA245211.a n ≠ n := by
  intro n hs hr
  exact no_fixed_count65 hs hr

end A245211New

theorem OMA.solution : OMA.R_OeisA245211_conjecture_R2_H3_R1.H1 := by
  exact A245211New.squarefree_no_fixed_count65
