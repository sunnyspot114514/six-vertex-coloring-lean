import OMAReductions.R_OeisA245211_conjecture_R2
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
# Finite modular obstructions for ten odd non-prime-power cycle lengths

Token positions distinguish repeated prime factors. Each listed position
normal form is proved complete by a closed finite proposition, checked by
Lean's kernel. The final finite exclusions use the same `positionTest` whose
soundness is proved in `A245211.Checker`.

The data generator and Python searches are discovery tools only. No external
computation, `native_decide`, extra axiom, or unchecked theorem is used here.
-/

namespace A245211New

/-! ## Six small cases -/
abbrev test15 (a b : Nat) : Bool :=
  positionTest 15 33 [(3, 0), (3, a), (11, b)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def exclude15 :
    ∀ a b : Fin 15, test15 a.val b.val = true → False := by
  decide +kernel
abbrev test21 (a : Nat) : Bool :=
  positionTest 21 3 [(3, 0), (3, a)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def exclude21 :
    ∀ a : Fin 21, test21 a.val = true → False := by
  decide +kernel
abbrev test33 (a b : Nat) : Bool :=
  positionTest 33 33 [(3, 0), (3, a), (683, b)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def exclude33 :
    ∀ a b : Fin 33, test33 a.val b.val = true → False := by
  decide +kernel
abbrev test39 (a : Nat) : Bool :=
  positionTest 39 3 [(3, 0), (3, a)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def exclude39 :
    ∀ a : Fin 39, test39 a.val = true → False := by
  decide +kernel
abbrev test57 (a : Nat) : Bool :=
  positionTest 57 3 [(3, 0), (3, a)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def exclude57 :
    ∀ a : Fin 57, test57 a.val = true → False := by
  decide +kernel
abbrev test63 (a b : Nat) : Bool :=
  positionTest 63 3 [(3, 0), (3, a), (3, b)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def exclude63 :
    ∀ a b : Fin 63, test63 a.val b.val = true → False := by
  decide +kernel
/-! ## Thirty-five factors -/
abbrev test35_5 (a : Nat) : Bool :=
  positionTest 35 5 [(3, 0), (43, a)]
abbrev test35_3 (b c d : Nat) : Bool :=
  positionTest 35 3 [(3, 0), (11, b), (281, c), (86171, d)]
abbrev test35 (q b a c d : Nat) : Bool :=
  positionTest 35 q [(3, 0), (11, b), (43, a), (281, c), (86171, d)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_5 :
    ∀ a : Fin 35, test35_5 a.val = true → a.val = 1 ∨ a.val = 34 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block0 :
    ∀ c d : Fin 35, test35_3 0 c.val d.val = true →
      (0 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 0 = d.val) ∨ (d.val = 1 ∧ 0 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block1 :
    ∀ c d : Fin 35, test35_3 1 c.val d.val = true →
      (1 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 1 = d.val) ∨ (d.val = 1 ∧ 1 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block2 :
    ∀ c d : Fin 35, test35_3 2 c.val d.val = true →
      (2 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 2 = d.val) ∨ (d.val = 1 ∧ 2 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block3 :
    ∀ c d : Fin 35, test35_3 3 c.val d.val = true →
      (3 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 3 = d.val) ∨ (d.val = 1 ∧ 3 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block4 :
    ∀ c d : Fin 35, test35_3 4 c.val d.val = true →
      (4 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 4 = d.val) ∨ (d.val = 1 ∧ 4 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block5 :
    ∀ c d : Fin 35, test35_3 5 c.val d.val = true →
      (5 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 5 = d.val) ∨ (d.val = 1 ∧ 5 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block6 :
    ∀ c d : Fin 35, test35_3 6 c.val d.val = true →
      (6 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 6 = d.val) ∨ (d.val = 1 ∧ 6 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block7 :
    ∀ c d : Fin 35, test35_3 7 c.val d.val = true →
      (7 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 7 = d.val) ∨ (d.val = 1 ∧ 7 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block8 :
    ∀ c d : Fin 35, test35_3 8 c.val d.val = true →
      (8 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 8 = d.val) ∨ (d.val = 1 ∧ 8 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block9 :
    ∀ c d : Fin 35, test35_3 9 c.val d.val = true →
      (9 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 9 = d.val) ∨ (d.val = 1 ∧ 9 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block10 :
    ∀ c d : Fin 35, test35_3 10 c.val d.val = true →
      (10 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 10 = d.val) ∨ (d.val = 1 ∧ 10 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block11 :
    ∀ c d : Fin 35, test35_3 11 c.val d.val = true →
      (11 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 11 = d.val) ∨ (d.val = 1 ∧ 11 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block12 :
    ∀ c d : Fin 35, test35_3 12 c.val d.val = true →
      (12 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 12 = d.val) ∨ (d.val = 1 ∧ 12 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block13 :
    ∀ c d : Fin 35, test35_3 13 c.val d.val = true →
      (13 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 13 = d.val) ∨ (d.val = 1 ∧ 13 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block14 :
    ∀ c d : Fin 35, test35_3 14 c.val d.val = true →
      (14 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 14 = d.val) ∨ (d.val = 1 ∧ 14 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block15 :
    ∀ c d : Fin 35, test35_3 15 c.val d.val = true →
      (15 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 15 = d.val) ∨ (d.val = 1 ∧ 15 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block16 :
    ∀ c d : Fin 35, test35_3 16 c.val d.val = true →
      (16 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 16 = d.val) ∨ (d.val = 1 ∧ 16 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block17 :
    ∀ c d : Fin 35, test35_3 17 c.val d.val = true →
      (17 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 17 = d.val) ∨ (d.val = 1 ∧ 17 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block18 :
    ∀ c d : Fin 35, test35_3 18 c.val d.val = true →
      (18 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 18 = d.val) ∨ (d.val = 1 ∧ 18 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block19 :
    ∀ c d : Fin 35, test35_3 19 c.val d.val = true →
      (19 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 19 = d.val) ∨ (d.val = 1 ∧ 19 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block20 :
    ∀ c d : Fin 35, test35_3 20 c.val d.val = true →
      (20 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 20 = d.val) ∨ (d.val = 1 ∧ 20 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block21 :
    ∀ c d : Fin 35, test35_3 21 c.val d.val = true →
      (21 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 21 = d.val) ∨ (d.val = 1 ∧ 21 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block22 :
    ∀ c d : Fin 35, test35_3 22 c.val d.val = true →
      (22 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 22 = d.val) ∨ (d.val = 1 ∧ 22 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block23 :
    ∀ c d : Fin 35, test35_3 23 c.val d.val = true →
      (23 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 23 = d.val) ∨ (d.val = 1 ∧ 23 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block24 :
    ∀ c d : Fin 35, test35_3 24 c.val d.val = true →
      (24 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 24 = d.val) ∨ (d.val = 1 ∧ 24 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block25 :
    ∀ c d : Fin 35, test35_3 25 c.val d.val = true →
      (25 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 25 = d.val) ∨ (d.val = 1 ∧ 25 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block26 :
    ∀ c d : Fin 35, test35_3 26 c.val d.val = true →
      (26 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 26 = d.val) ∨ (d.val = 1 ∧ 26 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block27 :
    ∀ c d : Fin 35, test35_3 27 c.val d.val = true →
      (27 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 27 = d.val) ∨ (d.val = 1 ∧ 27 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block28 :
    ∀ c d : Fin 35, test35_3 28 c.val d.val = true →
      (28 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 28 = d.val) ∨ (d.val = 1 ∧ 28 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block29 :
    ∀ c d : Fin 35, test35_3 29 c.val d.val = true →
      (29 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 29 = d.val) ∨ (d.val = 1 ∧ 29 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block30 :
    ∀ c d : Fin 35, test35_3 30 c.val d.val = true →
      (30 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 30 = d.val) ∨ (d.val = 1 ∧ 30 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block31 :
    ∀ c d : Fin 35, test35_3 31 c.val d.val = true →
      (31 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 31 = d.val) ∨ (d.val = 1 ∧ 31 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block32 :
    ∀ c d : Fin 35, test35_3 32 c.val d.val = true →
      (32 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 32 = d.val) ∨ (d.val = 1 ∧ 32 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block33 :
    ∀ c d : Fin 35, test35_3 33 c.val d.val = true →
      (33 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 33 = d.val) ∨ (d.val = 1 ∧ 33 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify35_3_block34 :
    ∀ c d : Fin 35, test35_3 34 c.val d.val = true →
      (34 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 34 = d.val) ∨ (d.val = 1 ∧ 34 = c.val) := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem classify35_3 (b : Fin 35) :
    ∀ c d : Fin 35, test35_3 b.val c.val d.val = true →
      (b.val = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ b.val = d.val) ∨ (d.val = 1 ∧ b.val = c.val) := by
  fin_cases b
  · simpa using classify35_3_block0
  · simpa using classify35_3_block1
  · simpa using classify35_3_block2
  · simpa using classify35_3_block3
  · simpa using classify35_3_block4
  · simpa using classify35_3_block5
  · simpa using classify35_3_block6
  · simpa using classify35_3_block7
  · simpa using classify35_3_block8
  · simpa using classify35_3_block9
  · simpa using classify35_3_block10
  · simpa using classify35_3_block11
  · simpa using classify35_3_block12
  · simpa using classify35_3_block13
  · simpa using classify35_3_block14
  · simpa using classify35_3_block15
  · simpa using classify35_3_block16
  · simpa using classify35_3_block17
  · simpa using classify35_3_block18
  · simpa using classify35_3_block19
  · simpa using classify35_3_block20
  · simpa using classify35_3_block21
  · simpa using classify35_3_block22
  · simpa using classify35_3_block23
  · simpa using classify35_3_block24
  · simpa using classify35_3_block25
  · simpa using classify35_3_block26
  · simpa using classify35_3_block27
  · simpa using classify35_3_block28
  · simpa using classify35_3_block29
  · simpa using classify35_3_block30
  · simpa using classify35_3_block31
  · simpa using classify35_3_block32
  · simpa using classify35_3_block33
  · simpa using classify35_3_block34

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude35_pattern0 :
    ∀ a t : Fin 35, (a.val = 1 ∨ a.val = 34) →
      test35 7 1 a.val t.val t.val = true →
      test35 11 1 a.val t.val t.val = true →
      test35 13 1 a.val t.val t.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude35_pattern1 :
    ∀ a t : Fin 35, (a.val = 1 ∨ a.val = 34) →
      test35 7 t.val a.val 1 t.val = true →
      test35 11 t.val a.val 1 t.val = true →
      test35 13 t.val a.val 1 t.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude35_pattern2 :
    ∀ a t : Fin 35, (a.val = 1 ∨ a.val = 34) →
      test35 7 t.val a.val t.val 1 = true →
      test35 11 t.val a.val t.val 1 = true →
      test35 13 t.val a.val t.val 1 = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem exclude35 (b a c d : Fin 35)
    (h5 : test35_5 a.val = true)
    (h3 : test35_3 b.val c.val d.val = true)
    (h7 : test35 7 b.val a.val c.val d.val = true)
    (h11 : test35 11 b.val a.val c.val d.val = true)
    (h13 : test35 13 b.val a.val c.val d.val = true) : False := by
  have ha := classify35_5 a h5
  rcases classify35_3 b c d h3 with ⟨hb, hcd⟩ | ⟨hc, hbd⟩ | ⟨hd, hbc⟩
  · exact exclude35_pattern0 a d ha
      (by simpa only [hb, hcd] using h7)
      (by simpa only [hb, hcd] using h11)
      (by simpa only [hb, hcd] using h13)
  · exact exclude35_pattern1 a d ha
      (by simpa only [hc, hbd] using h7)
      (by simpa only [hc, hbd] using h11)
      (by simpa only [hc, hbd] using h13)
  · exact exclude35_pattern2 a c ha
      (by simpa only [hd, hbc] using h7)
      (by simpa only [hd, hbc] using h11)
      (by simpa only [hd, hbc] using h13)
/-! ## Forty-five factors -/
def forms45_3 (i : Fin 13) : Nat × Nat × Nat :=
  ([(42, 43, 44),
    (42, 44, 43),
    (43, 42, 44),
    (43, 43, 44),
    (43, 44, 42),
    (43, 44, 43),
    (43, 44, 44),
    (44, 42, 43),
    (44, 43, 42),
    (44, 43, 43),
    (44, 43, 44),
    (44, 44, 43),
    (44, 44, 44)] : List (Nat × Nat × Nat))[i.val]!
def forms45_5 (i : Fin 13) : Nat × Nat × Nat × Nat :=
  ([(42, 43, 44, 1),
    (42, 44, 43, 1),
    (43, 42, 44, 1),
    (43, 44, 42, 1),
    (43, 44, 44, 1),
    (43, 44, 44, 43),
    (44, 42, 43, 1),
    (44, 43, 42, 1),
    (44, 43, 44, 1),
    (44, 43, 44, 43),
    (44, 44, 43, 1),
    (44, 44, 43, 43),
    (44, 44, 44, 0)] : List (Nat × Nat × Nat × Nat))[i.val]!
abbrev test45_3 (a b c : Nat) : Bool :=
  positionTest 45 3 [(3, a), (3, b), (3, c), (11, 0)]
abbrev test45_5 (a b c d : Nat) : Bool :=
  positionTest 45 5 [(3, a), (3, b), (3, c), (11, 0), (19, d)]
abbrev test45_7 (a b c d e : Nat) : Bool :=
  positionTest 45 7 [(3, a), (3, b), (3, c), (11, 0), (19, d), (331, e)]
abbrev test45 (q a b c d e f : Nat) : Bool :=
  positionTest 45 q [(3, a), (3, b), (3, c), (11, 0), (19, d), (331, e), (18837001, f)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem test45_neutral (a b c d e f : Nat) :
    test45 7 a b c d e f = test45_7 a b c d e := by
  exact positionTest_append_mod_one 45 7 (by decide)
    [(3, a), (3, b), (3, c), (11, 0), (19, d), (331, e)] []
    (18837001, f) (by change 18837001 % 7 = 1; decide)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block0 :
    ∀ b c : Fin 45, test45_3 0 b.val c.val = true →
      ∃ i : Fin 13, 0 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block1 :
    ∀ b c : Fin 45, test45_3 1 b.val c.val = true →
      ∃ i : Fin 13, 1 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block2 :
    ∀ b c : Fin 45, test45_3 2 b.val c.val = true →
      ∃ i : Fin 13, 2 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block3 :
    ∀ b c : Fin 45, test45_3 3 b.val c.val = true →
      ∃ i : Fin 13, 3 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block4 :
    ∀ b c : Fin 45, test45_3 4 b.val c.val = true →
      ∃ i : Fin 13, 4 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block5 :
    ∀ b c : Fin 45, test45_3 5 b.val c.val = true →
      ∃ i : Fin 13, 5 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block6 :
    ∀ b c : Fin 45, test45_3 6 b.val c.val = true →
      ∃ i : Fin 13, 6 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block7 :
    ∀ b c : Fin 45, test45_3 7 b.val c.val = true →
      ∃ i : Fin 13, 7 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block8 :
    ∀ b c : Fin 45, test45_3 8 b.val c.val = true →
      ∃ i : Fin 13, 8 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block9 :
    ∀ b c : Fin 45, test45_3 9 b.val c.val = true →
      ∃ i : Fin 13, 9 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block10 :
    ∀ b c : Fin 45, test45_3 10 b.val c.val = true →
      ∃ i : Fin 13, 10 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block11 :
    ∀ b c : Fin 45, test45_3 11 b.val c.val = true →
      ∃ i : Fin 13, 11 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block12 :
    ∀ b c : Fin 45, test45_3 12 b.val c.val = true →
      ∃ i : Fin 13, 12 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block13 :
    ∀ b c : Fin 45, test45_3 13 b.val c.val = true →
      ∃ i : Fin 13, 13 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block14 :
    ∀ b c : Fin 45, test45_3 14 b.val c.val = true →
      ∃ i : Fin 13, 14 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block15 :
    ∀ b c : Fin 45, test45_3 15 b.val c.val = true →
      ∃ i : Fin 13, 15 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block16 :
    ∀ b c : Fin 45, test45_3 16 b.val c.val = true →
      ∃ i : Fin 13, 16 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block17 :
    ∀ b c : Fin 45, test45_3 17 b.val c.val = true →
      ∃ i : Fin 13, 17 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block18 :
    ∀ b c : Fin 45, test45_3 18 b.val c.val = true →
      ∃ i : Fin 13, 18 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block19 :
    ∀ b c : Fin 45, test45_3 19 b.val c.val = true →
      ∃ i : Fin 13, 19 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block20 :
    ∀ b c : Fin 45, test45_3 20 b.val c.val = true →
      ∃ i : Fin 13, 20 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block21 :
    ∀ b c : Fin 45, test45_3 21 b.val c.val = true →
      ∃ i : Fin 13, 21 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block22 :
    ∀ b c : Fin 45, test45_3 22 b.val c.val = true →
      ∃ i : Fin 13, 22 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block23 :
    ∀ b c : Fin 45, test45_3 23 b.val c.val = true →
      ∃ i : Fin 13, 23 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block24 :
    ∀ b c : Fin 45, test45_3 24 b.val c.val = true →
      ∃ i : Fin 13, 24 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block25 :
    ∀ b c : Fin 45, test45_3 25 b.val c.val = true →
      ∃ i : Fin 13, 25 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block26 :
    ∀ b c : Fin 45, test45_3 26 b.val c.val = true →
      ∃ i : Fin 13, 26 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block27 :
    ∀ b c : Fin 45, test45_3 27 b.val c.val = true →
      ∃ i : Fin 13, 27 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block28 :
    ∀ b c : Fin 45, test45_3 28 b.val c.val = true →
      ∃ i : Fin 13, 28 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block29 :
    ∀ b c : Fin 45, test45_3 29 b.val c.val = true →
      ∃ i : Fin 13, 29 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block30 :
    ∀ b c : Fin 45, test45_3 30 b.val c.val = true →
      ∃ i : Fin 13, 30 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block31 :
    ∀ b c : Fin 45, test45_3 31 b.val c.val = true →
      ∃ i : Fin 13, 31 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block32 :
    ∀ b c : Fin 45, test45_3 32 b.val c.val = true →
      ∃ i : Fin 13, 32 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block33 :
    ∀ b c : Fin 45, test45_3 33 b.val c.val = true →
      ∃ i : Fin 13, 33 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block34 :
    ∀ b c : Fin 45, test45_3 34 b.val c.val = true →
      ∃ i : Fin 13, 34 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block35 :
    ∀ b c : Fin 45, test45_3 35 b.val c.val = true →
      ∃ i : Fin 13, 35 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block36 :
    ∀ b c : Fin 45, test45_3 36 b.val c.val = true →
      ∃ i : Fin 13, 36 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block37 :
    ∀ b c : Fin 45, test45_3 37 b.val c.val = true →
      ∃ i : Fin 13, 37 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block38 :
    ∀ b c : Fin 45, test45_3 38 b.val c.val = true →
      ∃ i : Fin 13, 38 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block39 :
    ∀ b c : Fin 45, test45_3 39 b.val c.val = true →
      ∃ i : Fin 13, 39 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block40 :
    ∀ b c : Fin 45, test45_3 40 b.val c.val = true →
      ∃ i : Fin 13, 40 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block41 :
    ∀ b c : Fin 45, test45_3 41 b.val c.val = true →
      ∃ i : Fin 13, 41 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block42 :
    ∀ b c : Fin 45, test45_3 42 b.val c.val = true →
      ∃ i : Fin 13, 42 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block43 :
    ∀ b c : Fin 45, test45_3 43 b.val c.val = true →
      ∃ i : Fin 13, 43 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_3_block44 :
    ∀ b c : Fin 45, test45_3 44 b.val c.val = true →
      ∃ i : Fin 13, 44 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem classify45_3 (a : Fin 45) :
    ∀ b c : Fin 45, test45_3 a.val b.val c.val = true →
      ∃ i : Fin 13, a.val = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  fin_cases a
  · simpa using classify45_3_block0
  · simpa using classify45_3_block1
  · simpa using classify45_3_block2
  · simpa using classify45_3_block3
  · simpa using classify45_3_block4
  · simpa using classify45_3_block5
  · simpa using classify45_3_block6
  · simpa using classify45_3_block7
  · simpa using classify45_3_block8
  · simpa using classify45_3_block9
  · simpa using classify45_3_block10
  · simpa using classify45_3_block11
  · simpa using classify45_3_block12
  · simpa using classify45_3_block13
  · simpa using classify45_3_block14
  · simpa using classify45_3_block15
  · simpa using classify45_3_block16
  · simpa using classify45_3_block17
  · simpa using classify45_3_block18
  · simpa using classify45_3_block19
  · simpa using classify45_3_block20
  · simpa using classify45_3_block21
  · simpa using classify45_3_block22
  · simpa using classify45_3_block23
  · simpa using classify45_3_block24
  · simpa using classify45_3_block25
  · simpa using classify45_3_block26
  · simpa using classify45_3_block27
  · simpa using classify45_3_block28
  · simpa using classify45_3_block29
  · simpa using classify45_3_block30
  · simpa using classify45_3_block31
  · simpa using classify45_3_block32
  · simpa using classify45_3_block33
  · simpa using classify45_3_block34
  · simpa using classify45_3_block35
  · simpa using classify45_3_block36
  · simpa using classify45_3_block37
  · simpa using classify45_3_block38
  · simpa using classify45_3_block39
  · simpa using classify45_3_block40
  · simpa using classify45_3_block41
  · simpa using classify45_3_block42
  · simpa using classify45_3_block43
  · simpa using classify45_3_block44

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify45_5 :
    ∀ (i : Fin 13) (d : Fin 45),
      test45_5 (forms45_3 i).1 (forms45_3 i).2.1 (forms45_3 i).2.2 d.val = true →
      ∃ j : Fin 13, (forms45_3 i).1 = (forms45_5 j).1 ∧
        (forms45_3 i).2.1 = (forms45_5 j).2.1 ∧
        (forms45_3 i).2.2 = (forms45_5 j).2.2.1 ∧
        d.val = (forms45_5 j).2.2.2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block0_slice0 :
    ∀ e : Fin 45, 0 ≤ e.val → e.val < 9 →
      test45_7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block0_slice1 :
    ∀ e : Fin 45, 9 ≤ e.val → e.val < 18 →
      test45_7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block0_slice2 :
    ∀ e : Fin 45, 18 ≤ e.val → e.val < 27 →
      test45_7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block0_slice3 :
    ∀ e : Fin 45, 27 ≤ e.val → e.val < 36 →
      test45_7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block0_slice4 :
    ∀ e : Fin 45, 36 ≤ e.val → e.val < 45 →
      test45_7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block0 (e : Fin 45) :
    test45_7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 9
  · exact exclude45_forms_block0_slice0 e (by omega) h0
  by_cases h1 : e.val < 18
  · exact exclude45_forms_block0_slice1 e (by omega) h1
  by_cases h2 : e.val < 27
  · exact exclude45_forms_block0_slice2 e (by omega) h2
  by_cases h3 : e.val < 36
  · exact exclude45_forms_block0_slice3 e (by omega) h3
  exact exclude45_forms_block0_slice4 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block1 :
    ∀ e : Fin 45,
      test45_7 (forms45_5 (1 : Fin 13)).1 (forms45_5 (1 : Fin 13)).2.1 (forms45_5 (1 : Fin 13)).2.2.1 (forms45_5 (1 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (1 : Fin 13)).1 (forms45_5 (1 : Fin 13)).2.1 (forms45_5 (1 : Fin 13)).2.2.1 (forms45_5 (1 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (1 : Fin 13)).1 (forms45_5 (1 : Fin 13)).2.1 (forms45_5 (1 : Fin 13)).2.2.1 (forms45_5 (1 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e h7 f h13 h19
  have hperm : List.Perm [(3, 42), (3, 44), (3, 43)] [(3, 42), (3, 43), (3, 44)] := by decide
  have ht7 : test45_7 42 44 43 1 e.val =
      test45_7 42 43 44 1 e.val :=
    positionTest_perm 45 7 (List.Perm.append_right [(11, 0), (19, 1), (331, e.val)] hperm)
  have htest (q : Nat) : test45 q 42 44 43 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)] hperm)
  exact exclude45_forms_block0 e (ht7.symm.trans h7) f
    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block2 :
    ∀ e : Fin 45,
      test45_7 (forms45_5 (2 : Fin 13)).1 (forms45_5 (2 : Fin 13)).2.1 (forms45_5 (2 : Fin 13)).2.2.1 (forms45_5 (2 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (2 : Fin 13)).1 (forms45_5 (2 : Fin 13)).2.1 (forms45_5 (2 : Fin 13)).2.2.1 (forms45_5 (2 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (2 : Fin 13)).1 (forms45_5 (2 : Fin 13)).2.1 (forms45_5 (2 : Fin 13)).2.2.1 (forms45_5 (2 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e h7 f h13 h19
  have hperm : List.Perm [(3, 43), (3, 42), (3, 44)] [(3, 42), (3, 43), (3, 44)] := by decide
  have ht7 : test45_7 43 42 44 1 e.val =
      test45_7 42 43 44 1 e.val :=
    positionTest_perm 45 7 (List.Perm.append_right [(11, 0), (19, 1), (331, e.val)] hperm)
  have htest (q : Nat) : test45 q 43 42 44 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)] hperm)
  exact exclude45_forms_block0 e (ht7.symm.trans h7) f
    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block3 :
    ∀ e : Fin 45,
      test45_7 (forms45_5 (3 : Fin 13)).1 (forms45_5 (3 : Fin 13)).2.1 (forms45_5 (3 : Fin 13)).2.2.1 (forms45_5 (3 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (3 : Fin 13)).1 (forms45_5 (3 : Fin 13)).2.1 (forms45_5 (3 : Fin 13)).2.2.1 (forms45_5 (3 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (3 : Fin 13)).1 (forms45_5 (3 : Fin 13)).2.1 (forms45_5 (3 : Fin 13)).2.2.1 (forms45_5 (3 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e h7 f h13 h19
  have hperm : List.Perm [(3, 43), (3, 44), (3, 42)] [(3, 42), (3, 43), (3, 44)] := by decide
  have ht7 : test45_7 43 44 42 1 e.val =
      test45_7 42 43 44 1 e.val :=
    positionTest_perm 45 7 (List.Perm.append_right [(11, 0), (19, 1), (331, e.val)] hperm)
  have htest (q : Nat) : test45 q 43 44 42 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)] hperm)
  exact exclude45_forms_block0 e (ht7.symm.trans h7) f
    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block4_slice0 :
    ∀ e : Fin 45, 0 ≤ e.val → e.val < 9 →
      test45_7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block4_slice1 :
    ∀ e : Fin 45, 9 ≤ e.val → e.val < 18 →
      test45_7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block4_slice2 :
    ∀ e : Fin 45, 18 ≤ e.val → e.val < 27 →
      test45_7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block4_slice3 :
    ∀ e : Fin 45, 27 ≤ e.val → e.val < 36 →
      test45_7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block4_slice4 :
    ∀ e : Fin 45, 36 ≤ e.val → e.val < 45 →
      test45_7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block4 (e : Fin 45) :
    test45_7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 9
  · exact exclude45_forms_block4_slice0 e (by omega) h0
  by_cases h1 : e.val < 18
  · exact exclude45_forms_block4_slice1 e (by omega) h1
  by_cases h2 : e.val < 27
  · exact exclude45_forms_block4_slice2 e (by omega) h2
  by_cases h3 : e.val < 36
  · exact exclude45_forms_block4_slice3 e (by omega) h3
  exact exclude45_forms_block4_slice4 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block5_slice0 :
    ∀ e : Fin 45, 0 ≤ e.val → e.val < 9 →
      test45_7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block5_slice1 :
    ∀ e : Fin 45, 9 ≤ e.val → e.val < 18 →
      test45_7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block5_slice2 :
    ∀ e : Fin 45, 18 ≤ e.val → e.val < 27 →
      test45_7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block5_slice3 :
    ∀ e : Fin 45, 27 ≤ e.val → e.val < 36 →
      test45_7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block5_slice4 :
    ∀ e : Fin 45, 36 ≤ e.val → e.val < 45 →
      test45_7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block5 (e : Fin 45) :
    test45_7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 9
  · exact exclude45_forms_block5_slice0 e (by omega) h0
  by_cases h1 : e.val < 18
  · exact exclude45_forms_block5_slice1 e (by omega) h1
  by_cases h2 : e.val < 27
  · exact exclude45_forms_block5_slice2 e (by omega) h2
  by_cases h3 : e.val < 36
  · exact exclude45_forms_block5_slice3 e (by omega) h3
  exact exclude45_forms_block5_slice4 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block6 :
    ∀ e : Fin 45,
      test45_7 (forms45_5 (6 : Fin 13)).1 (forms45_5 (6 : Fin 13)).2.1 (forms45_5 (6 : Fin 13)).2.2.1 (forms45_5 (6 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (6 : Fin 13)).1 (forms45_5 (6 : Fin 13)).2.1 (forms45_5 (6 : Fin 13)).2.2.1 (forms45_5 (6 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (6 : Fin 13)).1 (forms45_5 (6 : Fin 13)).2.1 (forms45_5 (6 : Fin 13)).2.2.1 (forms45_5 (6 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e h7 f h13 h19
  have hperm : List.Perm [(3, 44), (3, 42), (3, 43)] [(3, 42), (3, 43), (3, 44)] := by decide
  have ht7 : test45_7 44 42 43 1 e.val =
      test45_7 42 43 44 1 e.val :=
    positionTest_perm 45 7 (List.Perm.append_right [(11, 0), (19, 1), (331, e.val)] hperm)
  have htest (q : Nat) : test45 q 44 42 43 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)] hperm)
  exact exclude45_forms_block0 e (ht7.symm.trans h7) f
    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block7 :
    ∀ e : Fin 45,
      test45_7 (forms45_5 (7 : Fin 13)).1 (forms45_5 (7 : Fin 13)).2.1 (forms45_5 (7 : Fin 13)).2.2.1 (forms45_5 (7 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (7 : Fin 13)).1 (forms45_5 (7 : Fin 13)).2.1 (forms45_5 (7 : Fin 13)).2.2.1 (forms45_5 (7 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (7 : Fin 13)).1 (forms45_5 (7 : Fin 13)).2.1 (forms45_5 (7 : Fin 13)).2.2.1 (forms45_5 (7 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e h7 f h13 h19
  have hperm : List.Perm [(3, 44), (3, 43), (3, 42)] [(3, 42), (3, 43), (3, 44)] := by decide
  have ht7 : test45_7 44 43 42 1 e.val =
      test45_7 42 43 44 1 e.val :=
    positionTest_perm 45 7 (List.Perm.append_right [(11, 0), (19, 1), (331, e.val)] hperm)
  have htest (q : Nat) : test45 q 44 43 42 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)] hperm)
  exact exclude45_forms_block0 e (ht7.symm.trans h7) f
    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block8 :
    ∀ e : Fin 45,
      test45_7 (forms45_5 (8 : Fin 13)).1 (forms45_5 (8 : Fin 13)).2.1 (forms45_5 (8 : Fin 13)).2.2.1 (forms45_5 (8 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (8 : Fin 13)).1 (forms45_5 (8 : Fin 13)).2.1 (forms45_5 (8 : Fin 13)).2.2.1 (forms45_5 (8 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (8 : Fin 13)).1 (forms45_5 (8 : Fin 13)).2.1 (forms45_5 (8 : Fin 13)).2.2.1 (forms45_5 (8 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e h7 f h13 h19
  have hperm : List.Perm [(3, 44), (3, 43), (3, 44)] [(3, 43), (3, 44), (3, 44)] := by decide
  have ht7 : test45_7 44 43 44 1 e.val =
      test45_7 43 44 44 1 e.val :=
    positionTest_perm 45 7 (List.Perm.append_right [(11, 0), (19, 1), (331, e.val)] hperm)
  have htest (q : Nat) : test45 q 44 43 44 1 e.val f.val =
      test45 q 43 44 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)] hperm)
  exact exclude45_forms_block4 e (ht7.symm.trans h7) f
    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block9 :
    ∀ e : Fin 45,
      test45_7 (forms45_5 (9 : Fin 13)).1 (forms45_5 (9 : Fin 13)).2.1 (forms45_5 (9 : Fin 13)).2.2.1 (forms45_5 (9 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (9 : Fin 13)).1 (forms45_5 (9 : Fin 13)).2.1 (forms45_5 (9 : Fin 13)).2.2.1 (forms45_5 (9 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (9 : Fin 13)).1 (forms45_5 (9 : Fin 13)).2.1 (forms45_5 (9 : Fin 13)).2.2.1 (forms45_5 (9 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e h7 f h13 h19
  have hperm : List.Perm [(3, 44), (3, 43), (3, 44)] [(3, 43), (3, 44), (3, 44)] := by decide
  have ht7 : test45_7 44 43 44 43 e.val =
      test45_7 43 44 44 43 e.val :=
    positionTest_perm 45 7 (List.Perm.append_right [(11, 0), (19, 43), (331, e.val)] hperm)
  have htest (q : Nat) : test45 q 44 43 44 43 e.val f.val =
      test45 q 43 44 44 43 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 43), (331, e.val), (18837001, f.val)] hperm)
  exact exclude45_forms_block5 e (ht7.symm.trans h7) f
    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block10 :
    ∀ e : Fin 45,
      test45_7 (forms45_5 (10 : Fin 13)).1 (forms45_5 (10 : Fin 13)).2.1 (forms45_5 (10 : Fin 13)).2.2.1 (forms45_5 (10 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (10 : Fin 13)).1 (forms45_5 (10 : Fin 13)).2.1 (forms45_5 (10 : Fin 13)).2.2.1 (forms45_5 (10 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (10 : Fin 13)).1 (forms45_5 (10 : Fin 13)).2.1 (forms45_5 (10 : Fin 13)).2.2.1 (forms45_5 (10 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e h7 f h13 h19
  have hperm : List.Perm [(3, 44), (3, 44), (3, 43)] [(3, 43), (3, 44), (3, 44)] := by decide
  have ht7 : test45_7 44 44 43 1 e.val =
      test45_7 43 44 44 1 e.val :=
    positionTest_perm 45 7 (List.Perm.append_right [(11, 0), (19, 1), (331, e.val)] hperm)
  have htest (q : Nat) : test45 q 44 44 43 1 e.val f.val =
      test45 q 43 44 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)] hperm)
  exact exclude45_forms_block4 e (ht7.symm.trans h7) f
    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block11 :
    ∀ e : Fin 45,
      test45_7 (forms45_5 (11 : Fin 13)).1 (forms45_5 (11 : Fin 13)).2.1 (forms45_5 (11 : Fin 13)).2.2.1 (forms45_5 (11 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (11 : Fin 13)).1 (forms45_5 (11 : Fin 13)).2.1 (forms45_5 (11 : Fin 13)).2.2.1 (forms45_5 (11 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (11 : Fin 13)).1 (forms45_5 (11 : Fin 13)).2.1 (forms45_5 (11 : Fin 13)).2.2.1 (forms45_5 (11 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e h7 f h13 h19
  have hperm : List.Perm [(3, 44), (3, 44), (3, 43)] [(3, 43), (3, 44), (3, 44)] := by decide
  have ht7 : test45_7 44 44 43 43 e.val =
      test45_7 43 44 44 43 e.val :=
    positionTest_perm 45 7 (List.Perm.append_right [(11, 0), (19, 43), (331, e.val)] hperm)
  have htest (q : Nat) : test45 q 44 44 43 43 e.val f.val =
      test45 q 43 44 44 43 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 43), (331, e.val), (18837001, f.val)] hperm)
  exact exclude45_forms_block5 e (ht7.symm.trans h7) f
    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block12_slice0 :
    ∀ e : Fin 45, 0 ≤ e.val → e.val < 9 →
      test45_7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block12_slice1 :
    ∀ e : Fin 45, 9 ≤ e.val → e.val < 18 →
      test45_7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block12_slice2 :
    ∀ e : Fin 45, 18 ≤ e.val → e.val < 27 →
      test45_7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block12_slice3 :
    ∀ e : Fin 45, 27 ≤ e.val → e.val < 36 →
      test45_7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude45_forms_block12_slice4 :
    ∀ e : Fin 45, 36 ≤ e.val → e.val < 45 →
      test45_7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms_block12 (e : Fin 45) :
    test45_7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 9
  · exact exclude45_forms_block12_slice0 e (by omega) h0
  by_cases h1 : e.val < 18
  · exact exclude45_forms_block12_slice1 e (by omega) h1
  by_cases h2 : e.val < 27
  · exact exclude45_forms_block12_slice2 e (by omega) h2
  by_cases h3 : e.val < 36
  · exact exclude45_forms_block12_slice3 e (by omega) h3
  exact exclude45_forms_block12_slice4 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude45_forms (j : Fin 13) :
    ∀ e : Fin 45,
      test45_7 (forms45_5 j).1 (forms45_5 j).2.1 (forms45_5 j).2.2.1 (forms45_5 j).2.2.2 e.val = true →
      ∀ f : Fin 45,
      test45 13 (forms45_5 j).1 (forms45_5 j).2.1 (forms45_5 j).2.2.1 (forms45_5 j).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 j).1 (forms45_5 j).2.1 (forms45_5 j).2.2.1 (forms45_5 j).2.2.2 e.val f.val = true →
      False := by
  fin_cases j
  · simpa using exclude45_forms_block0
  · simpa using exclude45_forms_block1
  · simpa using exclude45_forms_block2
  · simpa using exclude45_forms_block3
  · simpa using exclude45_forms_block4
  · simpa using exclude45_forms_block5
  · simpa using exclude45_forms_block6
  · simpa using exclude45_forms_block7
  · simpa using exclude45_forms_block8
  · simpa using exclude45_forms_block9
  · simpa using exclude45_forms_block10
  · simpa using exclude45_forms_block11
  · simpa using exclude45_forms_block12

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem exclude45 (a b c d e f : Fin 45)
    (h3 : test45_3 a.val b.val c.val = true)
    (h5 : test45_5 a.val b.val c.val d.val = true)
    (h7 : test45 7 a.val b.val c.val d.val e.val f.val = true)
    (h13 : test45 13 a.val b.val c.val d.val e.val f.val = true)
    (h19 : test45 19 a.val b.val c.val d.val e.val f.val = true) : False := by
  have h7' : test45_7 a.val b.val c.val d.val e.val = true :=
    (test45_neutral a.val b.val c.val d.val e.val f.val).symm.trans h7
  obtain ⟨i, ha, hb, hc⟩ := classify45_3 a b c h3
  obtain ⟨j, hja, hjb, hjc, hjd⟩ := classify45_5 i d
    (by simpa only [ha, hb, hc] using h5)
  exact exclude45_forms j e
    (by simpa only [ha, hb, hc, hja, hjb, hjc, hjd] using h7') f
    (by simpa only [ha, hb, hc, hja, hjb, hjc, hjd] using h13)
    (by simpa only [ha, hb, hc, hja, hjb, hjc, hjd] using h19)
/-! ## Fifty-one factors -/
def forms51_3 (i : Fin 3) : Nat × Nat :=
  ([(49, 50),
    (50, 49),
    (50, 50)] : List (Nat × Nat))[i.val]!
abbrev test51_3 (a b : Nat) : Bool :=
  positionTest 51 3 [(3, a), (3, b), (43691, 0)]
abbrev test51_7 (a b c e : Nat) : Bool :=
  positionTest 51 7 [(3, a), (3, b), (307, c), (6529, e), (43691, 0)]
abbrev test51 (q a b c d e : Nat) : Bool :=
  positionTest 51 q [(3, a), (3, b), (307, c), (2857, d), (6529, e), (43691, 0)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block0 :
    ∀ b : Fin 51, test51_3 0 b.val = true →
      ∃ i : Fin 3, 0 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block1 :
    ∀ b : Fin 51, test51_3 1 b.val = true →
      ∃ i : Fin 3, 1 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block2 :
    ∀ b : Fin 51, test51_3 2 b.val = true →
      ∃ i : Fin 3, 2 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block3 :
    ∀ b : Fin 51, test51_3 3 b.val = true →
      ∃ i : Fin 3, 3 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block4 :
    ∀ b : Fin 51, test51_3 4 b.val = true →
      ∃ i : Fin 3, 4 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block5 :
    ∀ b : Fin 51, test51_3 5 b.val = true →
      ∃ i : Fin 3, 5 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block6 :
    ∀ b : Fin 51, test51_3 6 b.val = true →
      ∃ i : Fin 3, 6 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block7 :
    ∀ b : Fin 51, test51_3 7 b.val = true →
      ∃ i : Fin 3, 7 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block8 :
    ∀ b : Fin 51, test51_3 8 b.val = true →
      ∃ i : Fin 3, 8 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block9 :
    ∀ b : Fin 51, test51_3 9 b.val = true →
      ∃ i : Fin 3, 9 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block10 :
    ∀ b : Fin 51, test51_3 10 b.val = true →
      ∃ i : Fin 3, 10 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block11 :
    ∀ b : Fin 51, test51_3 11 b.val = true →
      ∃ i : Fin 3, 11 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block12 :
    ∀ b : Fin 51, test51_3 12 b.val = true →
      ∃ i : Fin 3, 12 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block13 :
    ∀ b : Fin 51, test51_3 13 b.val = true →
      ∃ i : Fin 3, 13 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block14 :
    ∀ b : Fin 51, test51_3 14 b.val = true →
      ∃ i : Fin 3, 14 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block15 :
    ∀ b : Fin 51, test51_3 15 b.val = true →
      ∃ i : Fin 3, 15 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block16 :
    ∀ b : Fin 51, test51_3 16 b.val = true →
      ∃ i : Fin 3, 16 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block17 :
    ∀ b : Fin 51, test51_3 17 b.val = true →
      ∃ i : Fin 3, 17 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block18 :
    ∀ b : Fin 51, test51_3 18 b.val = true →
      ∃ i : Fin 3, 18 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block19 :
    ∀ b : Fin 51, test51_3 19 b.val = true →
      ∃ i : Fin 3, 19 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block20 :
    ∀ b : Fin 51, test51_3 20 b.val = true →
      ∃ i : Fin 3, 20 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block21 :
    ∀ b : Fin 51, test51_3 21 b.val = true →
      ∃ i : Fin 3, 21 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block22 :
    ∀ b : Fin 51, test51_3 22 b.val = true →
      ∃ i : Fin 3, 22 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block23 :
    ∀ b : Fin 51, test51_3 23 b.val = true →
      ∃ i : Fin 3, 23 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block24 :
    ∀ b : Fin 51, test51_3 24 b.val = true →
      ∃ i : Fin 3, 24 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block25 :
    ∀ b : Fin 51, test51_3 25 b.val = true →
      ∃ i : Fin 3, 25 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block26 :
    ∀ b : Fin 51, test51_3 26 b.val = true →
      ∃ i : Fin 3, 26 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block27 :
    ∀ b : Fin 51, test51_3 27 b.val = true →
      ∃ i : Fin 3, 27 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block28 :
    ∀ b : Fin 51, test51_3 28 b.val = true →
      ∃ i : Fin 3, 28 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block29 :
    ∀ b : Fin 51, test51_3 29 b.val = true →
      ∃ i : Fin 3, 29 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block30 :
    ∀ b : Fin 51, test51_3 30 b.val = true →
      ∃ i : Fin 3, 30 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block31 :
    ∀ b : Fin 51, test51_3 31 b.val = true →
      ∃ i : Fin 3, 31 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block32 :
    ∀ b : Fin 51, test51_3 32 b.val = true →
      ∃ i : Fin 3, 32 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block33 :
    ∀ b : Fin 51, test51_3 33 b.val = true →
      ∃ i : Fin 3, 33 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block34 :
    ∀ b : Fin 51, test51_3 34 b.val = true →
      ∃ i : Fin 3, 34 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block35 :
    ∀ b : Fin 51, test51_3 35 b.val = true →
      ∃ i : Fin 3, 35 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block36 :
    ∀ b : Fin 51, test51_3 36 b.val = true →
      ∃ i : Fin 3, 36 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block37 :
    ∀ b : Fin 51, test51_3 37 b.val = true →
      ∃ i : Fin 3, 37 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block38 :
    ∀ b : Fin 51, test51_3 38 b.val = true →
      ∃ i : Fin 3, 38 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block39 :
    ∀ b : Fin 51, test51_3 39 b.val = true →
      ∃ i : Fin 3, 39 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block40 :
    ∀ b : Fin 51, test51_3 40 b.val = true →
      ∃ i : Fin 3, 40 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block41 :
    ∀ b : Fin 51, test51_3 41 b.val = true →
      ∃ i : Fin 3, 41 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block42 :
    ∀ b : Fin 51, test51_3 42 b.val = true →
      ∃ i : Fin 3, 42 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block43 :
    ∀ b : Fin 51, test51_3 43 b.val = true →
      ∃ i : Fin 3, 43 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block44 :
    ∀ b : Fin 51, test51_3 44 b.val = true →
      ∃ i : Fin 3, 44 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block45 :
    ∀ b : Fin 51, test51_3 45 b.val = true →
      ∃ i : Fin 3, 45 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block46 :
    ∀ b : Fin 51, test51_3 46 b.val = true →
      ∃ i : Fin 3, 46 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block47 :
    ∀ b : Fin 51, test51_3 47 b.val = true →
      ∃ i : Fin 3, 47 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block48 :
    ∀ b : Fin 51, test51_3 48 b.val = true →
      ∃ i : Fin 3, 48 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block49 :
    ∀ b : Fin 51, test51_3 49 b.val = true →
      ∃ i : Fin 3, 49 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify51_3_block50 :
    ∀ b : Fin 51, test51_3 50 b.val = true →
      ∃ i : Fin 3, 50 = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem classify51_3 (a : Fin 51) :
    ∀ b : Fin 51, test51_3 a.val b.val = true →
      ∃ i : Fin 3, a.val = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  fin_cases a
  · simpa using classify51_3_block0
  · simpa using classify51_3_block1
  · simpa using classify51_3_block2
  · simpa using classify51_3_block3
  · simpa using classify51_3_block4
  · simpa using classify51_3_block5
  · simpa using classify51_3_block6
  · simpa using classify51_3_block7
  · simpa using classify51_3_block8
  · simpa using classify51_3_block9
  · simpa using classify51_3_block10
  · simpa using classify51_3_block11
  · simpa using classify51_3_block12
  · simpa using classify51_3_block13
  · simpa using classify51_3_block14
  · simpa using classify51_3_block15
  · simpa using classify51_3_block16
  · simpa using classify51_3_block17
  · simpa using classify51_3_block18
  · simpa using classify51_3_block19
  · simpa using classify51_3_block20
  · simpa using classify51_3_block21
  · simpa using classify51_3_block22
  · simpa using classify51_3_block23
  · simpa using classify51_3_block24
  · simpa using classify51_3_block25
  · simpa using classify51_3_block26
  · simpa using classify51_3_block27
  · simpa using classify51_3_block28
  · simpa using classify51_3_block29
  · simpa using classify51_3_block30
  · simpa using classify51_3_block31
  · simpa using classify51_3_block32
  · simpa using classify51_3_block33
  · simpa using classify51_3_block34
  · simpa using classify51_3_block35
  · simpa using classify51_3_block36
  · simpa using classify51_3_block37
  · simpa using classify51_3_block38
  · simpa using classify51_3_block39
  · simpa using classify51_3_block40
  · simpa using classify51_3_block41
  · simpa using classify51_3_block42
  · simpa using classify51_3_block43
  · simpa using classify51_3_block44
  · simpa using classify51_3_block45
  · simpa using classify51_3_block46
  · simpa using classify51_3_block47
  · simpa using classify51_3_block48
  · simpa using classify51_3_block49
  · simpa using classify51_3_block50

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot0_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 20 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot0_slice1 :
    ∀ e : Fin 51, 20 ≤ e.val → e.val < 44 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot0_slice2 :
    ∀ e : Fin 51, 44 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot0 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 20
  · exact exclude51_forms_block0_slot0_slice0 e (by omega) h0
  by_cases h1 : e.val < 44
  · exact exclude51_forms_block0_slot0_slice1 e (by omega) h1
  exact exclude51_forms_block0_slot0_slice2 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot1_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 25 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot1_slice1 :
    ∀ e : Fin 51, 25 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot1 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 25
  · exact exclude51_forms_block0_slot1_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot1_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot2 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 2 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 2 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 2 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 2 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot3 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 3 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 3 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 3 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 3 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot4 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 4 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 4 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 4 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 4 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot5 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 5 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 5 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 5 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 5 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot6 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 6 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 6 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 6 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 6 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot7 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 7 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 7 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 7 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 7 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot8 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 8 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 8 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 8 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 8 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot9 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 9 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 9 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 9 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 9 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot10 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 10 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 10 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 10 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 10 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot11 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 11 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 11 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 11 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 11 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot12 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 12 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 12 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 12 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 12 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot13 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 13 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 13 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 13 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 13 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot14 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 14 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 14 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 14 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 14 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot15 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 15 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 15 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 15 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 15 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot16 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 16 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 16 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 16 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 16 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot17 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 17 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 17 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 17 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 17 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot18 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 18 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 18 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 18 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 18 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot19 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 19 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 19 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 19 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 19 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot20 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 20 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 20 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 20 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 20 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot21 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 21 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 21 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 21 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 21 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot22 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 22 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 22 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 22 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 22 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot23 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 23 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 23 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 23 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 23 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot24_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot24_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot24 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block0_slot24_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot24_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot25 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 25 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 25 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 25 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 25 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot26 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 26 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 26 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 26 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 26 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot27_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot27_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot27 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block0_slot27_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot27_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot28_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot28_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot28 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 24
  · exact exclude51_forms_block0_slot28_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot28_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot29 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 29 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 29 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 29 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 29 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot30_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot30_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot30 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block0_slot30_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot30_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot31_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot31_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot31 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 24
  · exact exclude51_forms_block0_slot31_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot31_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot32 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 32 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 32 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 32 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 32 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot33_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot33_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot33 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block0_slot33_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot33_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot34_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot34_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot34 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 24
  · exact exclude51_forms_block0_slot34_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot34_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot35 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 35 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 35 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 35 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 35 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot36_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot36_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot36 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block0_slot36_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot36_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot37_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot37_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot37 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 24
  · exact exclude51_forms_block0_slot37_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot37_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot38 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 38 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 38 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 38 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 38 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot39_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot39_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot39 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block0_slot39_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot39_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot40_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot40_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot40 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 24
  · exact exclude51_forms_block0_slot40_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot40_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot41 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 41 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 41 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 41 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 41 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot42_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot42_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot42 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block0_slot42_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot42_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot43_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot43_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot43 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 24
  · exact exclude51_forms_block0_slot43_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot43_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot44 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 44 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 44 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 44 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 44 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot45_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot45_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot45 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block0_slot45_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot45_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot46_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot46_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot46 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 24
  · exact exclude51_forms_block0_slot46_slice0 e (by omega) h0
  exact exclude51_forms_block0_slot46_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot47 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 47 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 47 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 47 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 47 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot48_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot48_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 46 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot48_slice2 :
    ∀ e : Fin 51, 46 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot48 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block0_slot48_slice0 e (by omega) h0
  by_cases h1 : e.val < 46
  · exact exclude51_forms_block0_slot48_slice1 e (by omega) h1
  exact exclude51_forms_block0_slot48_slice2 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot49_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 12 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot49_slice1 :
    ∀ e : Fin 51, 12 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot49_slice2 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 36 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot49_slice3 :
    ∀ e : Fin 51, 36 ≤ e.val → e.val < 48 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot49_slice4 :
    ∀ e : Fin 51, 48 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0_slot49 (e : Fin 51) :
    test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 12
  · exact exclude51_forms_block0_slot49_slice0 e (by omega) h0
  by_cases h1 : e.val < 24
  · exact exclude51_forms_block0_slot49_slice1 e (by omega) h1
  by_cases h2 : e.val < 36
  · exact exclude51_forms_block0_slot49_slice2 e (by omega) h2
  by_cases h3 : e.val < 48
  · exact exclude51_forms_block0_slot49_slice3 e (by omega) h3
  exact exclude51_forms_block0_slot49_slice4 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block0_slot50 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block0 (c : Fin 51) :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 c.val e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 c.val d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 c.val d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 c.val d.val e.val = true →
      False := by
  fin_cases c
  · simpa using exclude51_forms_block0_slot0
  · simpa using exclude51_forms_block0_slot1
  · simpa using exclude51_forms_block0_slot2
  · simpa using exclude51_forms_block0_slot3
  · simpa using exclude51_forms_block0_slot4
  · simpa using exclude51_forms_block0_slot5
  · simpa using exclude51_forms_block0_slot6
  · simpa using exclude51_forms_block0_slot7
  · simpa using exclude51_forms_block0_slot8
  · simpa using exclude51_forms_block0_slot9
  · simpa using exclude51_forms_block0_slot10
  · simpa using exclude51_forms_block0_slot11
  · simpa using exclude51_forms_block0_slot12
  · simpa using exclude51_forms_block0_slot13
  · simpa using exclude51_forms_block0_slot14
  · simpa using exclude51_forms_block0_slot15
  · simpa using exclude51_forms_block0_slot16
  · simpa using exclude51_forms_block0_slot17
  · simpa using exclude51_forms_block0_slot18
  · simpa using exclude51_forms_block0_slot19
  · simpa using exclude51_forms_block0_slot20
  · simpa using exclude51_forms_block0_slot21
  · simpa using exclude51_forms_block0_slot22
  · simpa using exclude51_forms_block0_slot23
  · simpa using exclude51_forms_block0_slot24
  · simpa using exclude51_forms_block0_slot25
  · simpa using exclude51_forms_block0_slot26
  · simpa using exclude51_forms_block0_slot27
  · simpa using exclude51_forms_block0_slot28
  · simpa using exclude51_forms_block0_slot29
  · simpa using exclude51_forms_block0_slot30
  · simpa using exclude51_forms_block0_slot31
  · simpa using exclude51_forms_block0_slot32
  · simpa using exclude51_forms_block0_slot33
  · simpa using exclude51_forms_block0_slot34
  · simpa using exclude51_forms_block0_slot35
  · simpa using exclude51_forms_block0_slot36
  · simpa using exclude51_forms_block0_slot37
  · simpa using exclude51_forms_block0_slot38
  · simpa using exclude51_forms_block0_slot39
  · simpa using exclude51_forms_block0_slot40
  · simpa using exclude51_forms_block0_slot41
  · simpa using exclude51_forms_block0_slot42
  · simpa using exclude51_forms_block0_slot43
  · simpa using exclude51_forms_block0_slot44
  · simpa using exclude51_forms_block0_slot45
  · simpa using exclude51_forms_block0_slot46
  · simpa using exclude51_forms_block0_slot47
  · simpa using exclude51_forms_block0_slot48
  · simpa using exclude51_forms_block0_slot49
  · simpa using exclude51_forms_block0_slot50

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block1 :
    ∀ c : Fin 51,
      ∀ e : Fin 51, test51_7 (forms51_3 (1 : Fin 3)).1 (forms51_3 (1 : Fin 3)).2 c.val e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (1 : Fin 3)).1 (forms51_3 (1 : Fin 3)).2 c.val d.val e.val = true →
      test51 11 (forms51_3 (1 : Fin 3)).1 (forms51_3 (1 : Fin 3)).2 c.val d.val e.val = true →
      test51 13 (forms51_3 (1 : Fin 3)).1 (forms51_3 (1 : Fin 3)).2 c.val d.val e.val = true →
      False := by
  intro c e h7 d h5 h11 h13
  have hperm : List.Perm [(3, 50), (3, 49)] [(3, 49), (3, 50)] := by decide
  have ht7 : test51_7 50 49 c.val e.val =
      test51_7 49 50 c.val e.val :=
    positionTest_perm 51 7 (List.Perm.append_right [(307, c.val), (6529, e.val), (43691, 0)] hperm)
  have htest (q : Nat) : test51 q 50 49 c.val d.val e.val =
      test51 q 49 50 c.val d.val e.val :=
    positionTest_perm 51 q (List.Perm.append_right [(307, c.val), (2857, d.val), (6529, e.val), (43691, 0)] hperm)
  exact exclude51_forms_block0 c e (ht7.symm.trans h7) d
    ((htest 5).symm.trans h5) ((htest 11).symm.trans h11) ((htest 13).symm.trans h13)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot0 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 0 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 0 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 0 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 0 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot1 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 1 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 1 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 1 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot2 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 2 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 2 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 2 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 2 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot3 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 3 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 3 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 3 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 3 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot4 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 4 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 4 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 4 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 4 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot5 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 5 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 5 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 5 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 5 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot6 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 6 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 6 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 6 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 6 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot7 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 7 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 7 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 7 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 7 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot8 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 8 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 8 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 8 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 8 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot9 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 9 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 9 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 9 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 9 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot10 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 10 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 10 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 10 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 10 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot11 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 11 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 11 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 11 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 11 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot12 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 12 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 12 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 12 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 12 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot13 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 13 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 13 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 13 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 13 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot14 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 14 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 14 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 14 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 14 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot15 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 15 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 15 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 15 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 15 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot16 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 16 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 16 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 16 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 16 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot17 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 17 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 17 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 17 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 17 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot18 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 18 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 18 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 18 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 18 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot19 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 19 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 19 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 19 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 19 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot20 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 20 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 20 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 20 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 20 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot21 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 21 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 21 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 21 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 21 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot22 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 22 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 22 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 22 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 22 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot23 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 23 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 23 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 23 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 23 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot24 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 24 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 24 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 24 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 24 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot25_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot25_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot25 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 23
  · exact exclude51_forms_block2_slot25_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot25_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot26_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot26_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot26 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block2_slot26_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot26_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot27 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 27 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 27 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 27 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 27 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot28_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot28_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot28 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 23
  · exact exclude51_forms_block2_slot28_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot28_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot29_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot29_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot29 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block2_slot29_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot29_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot30 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 30 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 30 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 30 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 30 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot31_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot31_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot31 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 23
  · exact exclude51_forms_block2_slot31_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot31_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot32_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot32_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot32 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block2_slot32_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot32_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot33 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 33 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 33 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 33 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 33 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot34_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot34_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot34 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 23
  · exact exclude51_forms_block2_slot34_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot34_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot35_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot35_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot35 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block2_slot35_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot35_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot36 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 36 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 36 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 36 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 36 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot37_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot37_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot37 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 23
  · exact exclude51_forms_block2_slot37_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot37_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot38_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot38_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot38 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block2_slot38_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot38_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot39 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 39 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 39 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 39 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 39 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot40_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot40_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot40 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 23
  · exact exclude51_forms_block2_slot40_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot40_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot41_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot41_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot41 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block2_slot41_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot41_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot42 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 42 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 42 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 42 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 42 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot43_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot43_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot43 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 23
  · exact exclude51_forms_block2_slot43_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot43_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot44_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot44_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot44 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block2_slot44_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot44_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot45 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 45 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 45 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 45 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 45 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot46_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot46_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot46 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 23
  · exact exclude51_forms_block2_slot46_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot46_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot47_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot47_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot47 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 22
  · exact exclude51_forms_block2_slot47_slice0 e (by omega) h0
  exact exclude51_forms_block2_slot47_slice1 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot48 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 48 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 48 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 48 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 48 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot49_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot49_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 47 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot49_slice2 :
    ∀ e : Fin 51, 47 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot49 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 23
  · exact exclude51_forms_block2_slot49_slice0 e (by omega) h0
  by_cases h1 : e.val < 47
  · exact exclude51_forms_block2_slot49_slice1 e (by omega) h1
  exact exclude51_forms_block2_slot49_slice2 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot50_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 11 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot50_slice1 :
    ∀ e : Fin 51, 11 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot50_slice2 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 35 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot50_slice3 :
    ∀ e : Fin 51, 35 ≤ e.val → e.val < 47 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude51_forms_block2_slot50_slice4 :
    ∀ e : Fin 51, 47 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2_slot50 (e : Fin 51) :
    test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  have hbound := e.isLt
  by_cases h0 : e.val < 11
  · exact exclude51_forms_block2_slot50_slice0 e (by omega) h0
  by_cases h1 : e.val < 23
  · exact exclude51_forms_block2_slot50_slice1 e (by omega) h1
  by_cases h2 : e.val < 35
  · exact exclude51_forms_block2_slot50_slice2 e (by omega) h2
  by_cases h3 : e.val < 47
  · exact exclude51_forms_block2_slot50_slice3 e (by omega) h3
  exact exclude51_forms_block2_slot50_slice4 e (by omega) (by omega)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms_block2 (c : Fin 51) :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 c.val e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 c.val d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 c.val d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 c.val d.val e.val = true →
      False := by
  fin_cases c
  · simpa using exclude51_forms_block2_slot0
  · simpa using exclude51_forms_block2_slot1
  · simpa using exclude51_forms_block2_slot2
  · simpa using exclude51_forms_block2_slot3
  · simpa using exclude51_forms_block2_slot4
  · simpa using exclude51_forms_block2_slot5
  · simpa using exclude51_forms_block2_slot6
  · simpa using exclude51_forms_block2_slot7
  · simpa using exclude51_forms_block2_slot8
  · simpa using exclude51_forms_block2_slot9
  · simpa using exclude51_forms_block2_slot10
  · simpa using exclude51_forms_block2_slot11
  · simpa using exclude51_forms_block2_slot12
  · simpa using exclude51_forms_block2_slot13
  · simpa using exclude51_forms_block2_slot14
  · simpa using exclude51_forms_block2_slot15
  · simpa using exclude51_forms_block2_slot16
  · simpa using exclude51_forms_block2_slot17
  · simpa using exclude51_forms_block2_slot18
  · simpa using exclude51_forms_block2_slot19
  · simpa using exclude51_forms_block2_slot20
  · simpa using exclude51_forms_block2_slot21
  · simpa using exclude51_forms_block2_slot22
  · simpa using exclude51_forms_block2_slot23
  · simpa using exclude51_forms_block2_slot24
  · simpa using exclude51_forms_block2_slot25
  · simpa using exclude51_forms_block2_slot26
  · simpa using exclude51_forms_block2_slot27
  · simpa using exclude51_forms_block2_slot28
  · simpa using exclude51_forms_block2_slot29
  · simpa using exclude51_forms_block2_slot30
  · simpa using exclude51_forms_block2_slot31
  · simpa using exclude51_forms_block2_slot32
  · simpa using exclude51_forms_block2_slot33
  · simpa using exclude51_forms_block2_slot34
  · simpa using exclude51_forms_block2_slot35
  · simpa using exclude51_forms_block2_slot36
  · simpa using exclude51_forms_block2_slot37
  · simpa using exclude51_forms_block2_slot38
  · simpa using exclude51_forms_block2_slot39
  · simpa using exclude51_forms_block2_slot40
  · simpa using exclude51_forms_block2_slot41
  · simpa using exclude51_forms_block2_slot42
  · simpa using exclude51_forms_block2_slot43
  · simpa using exclude51_forms_block2_slot44
  · simpa using exclude51_forms_block2_slot45
  · simpa using exclude51_forms_block2_slot46
  · simpa using exclude51_forms_block2_slot47
  · simpa using exclude51_forms_block2_slot48
  · simpa using exclude51_forms_block2_slot49
  · simpa using exclude51_forms_block2_slot50

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude51_forms (i : Fin 3) :
    ∀ c : Fin 51,
      ∀ e : Fin 51, test51_7 (forms51_3 i).1 (forms51_3 i).2 c.val e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 i).1 (forms51_3 i).2 c.val d.val e.val = true →
      test51 11 (forms51_3 i).1 (forms51_3 i).2 c.val d.val e.val = true →
      test51 13 (forms51_3 i).1 (forms51_3 i).2 c.val d.val e.val = true →
      False := by
  fin_cases i
  · simpa using exclude51_forms_block0
  · simpa using exclude51_forms_block1
  · simpa using exclude51_forms_block2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem exclude51 (a b c d e : Fin 51)
    (h3 : test51_3 a.val b.val = true)
    (h7 : test51_7 a.val b.val c.val e.val = true)
    (h5 : test51 5 a.val b.val c.val d.val e.val = true)
    (h11 : test51 11 a.val b.val c.val d.val e.val = true)
    (h13 : test51 13 a.val b.val c.val d.val e.val = true) : False := by
  obtain ⟨i, ha, hb⟩ := classify51_3 a b h3
  exact exclude51_forms i c e (by simpa only [ha, hb] using h7) d
    (by simpa only [ha, hb] using h5)
    (by simpa only [ha, hb] using h11)
    (by simpa only [ha, hb] using h13)
/-! ## Fifty-five factors -/
def forms55_11 (i : Fin 19) : Nat × Nat :=
  ([(39, 48),
    (40, 48),
    (41, 48),
    (42, 48),
    (43, 48),
    (44, 48),
    (45, 48),
    (46, 48),
    (47, 48),
    (48, 39),
    (48, 40),
    (48, 41),
    (48, 42),
    (48, 43),
    (48, 44),
    (48, 45),
    (48, 46),
    (48, 47),
    (48, 48)] : List (Nat × Nat))[i.val]!
abbrev test55_5 (a : Nat) : Bool :=
  positionTest 55 5 [(3, 0), (683, a)]
abbrev test55_11 (b c : Nat) : Bool :=
  positionTest 55 11 [(3, 0), (11, b), (11, c)]
abbrev test55_3 (b c a e : Nat) : Bool :=
  positionTest 55 3 [(3, 0), (11, b), (11, c), (683, a), (48912491, e)]
abbrev test55 (q b c a d e : Nat) : Bool :=
  positionTest 55 q [(3, 0), (11, b), (11, c), (683, a), (2971, d), (48912491, e)]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem test55_neutral (b c a d e : Nat) :
    test55 3 b c a d e = test55_3 b c a e := by
  exact positionTest_append_mod_one 55 3 (by decide)
    [(3, 0), (11, b), (11, c), (683, a)] [(48912491, e)]
    (2971, d) (by change 2971 % 3 = 1; decide)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_5 :
    ∀ a : Fin 55, test55_5 a.val = true → a.val = 1 ∨ a.val = 54 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block0 :
    ∀ c : Fin 55, test55_11 0 c.val = true →
      ∃ i : Fin 19, 0 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block1 :
    ∀ c : Fin 55, test55_11 1 c.val = true →
      ∃ i : Fin 19, 1 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block2 :
    ∀ c : Fin 55, test55_11 2 c.val = true →
      ∃ i : Fin 19, 2 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block3 :
    ∀ c : Fin 55, test55_11 3 c.val = true →
      ∃ i : Fin 19, 3 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block4 :
    ∀ c : Fin 55, test55_11 4 c.val = true →
      ∃ i : Fin 19, 4 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block5 :
    ∀ c : Fin 55, test55_11 5 c.val = true →
      ∃ i : Fin 19, 5 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block6 :
    ∀ c : Fin 55, test55_11 6 c.val = true →
      ∃ i : Fin 19, 6 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block7 :
    ∀ c : Fin 55, test55_11 7 c.val = true →
      ∃ i : Fin 19, 7 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block8 :
    ∀ c : Fin 55, test55_11 8 c.val = true →
      ∃ i : Fin 19, 8 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block9 :
    ∀ c : Fin 55, test55_11 9 c.val = true →
      ∃ i : Fin 19, 9 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block10 :
    ∀ c : Fin 55, test55_11 10 c.val = true →
      ∃ i : Fin 19, 10 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block11 :
    ∀ c : Fin 55, test55_11 11 c.val = true →
      ∃ i : Fin 19, 11 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block12 :
    ∀ c : Fin 55, test55_11 12 c.val = true →
      ∃ i : Fin 19, 12 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block13 :
    ∀ c : Fin 55, test55_11 13 c.val = true →
      ∃ i : Fin 19, 13 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block14 :
    ∀ c : Fin 55, test55_11 14 c.val = true →
      ∃ i : Fin 19, 14 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block15 :
    ∀ c : Fin 55, test55_11 15 c.val = true →
      ∃ i : Fin 19, 15 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block16 :
    ∀ c : Fin 55, test55_11 16 c.val = true →
      ∃ i : Fin 19, 16 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block17 :
    ∀ c : Fin 55, test55_11 17 c.val = true →
      ∃ i : Fin 19, 17 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block18 :
    ∀ c : Fin 55, test55_11 18 c.val = true →
      ∃ i : Fin 19, 18 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block19 :
    ∀ c : Fin 55, test55_11 19 c.val = true →
      ∃ i : Fin 19, 19 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block20 :
    ∀ c : Fin 55, test55_11 20 c.val = true →
      ∃ i : Fin 19, 20 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block21 :
    ∀ c : Fin 55, test55_11 21 c.val = true →
      ∃ i : Fin 19, 21 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block22 :
    ∀ c : Fin 55, test55_11 22 c.val = true →
      ∃ i : Fin 19, 22 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block23 :
    ∀ c : Fin 55, test55_11 23 c.val = true →
      ∃ i : Fin 19, 23 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block24 :
    ∀ c : Fin 55, test55_11 24 c.val = true →
      ∃ i : Fin 19, 24 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block25 :
    ∀ c : Fin 55, test55_11 25 c.val = true →
      ∃ i : Fin 19, 25 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block26 :
    ∀ c : Fin 55, test55_11 26 c.val = true →
      ∃ i : Fin 19, 26 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block27 :
    ∀ c : Fin 55, test55_11 27 c.val = true →
      ∃ i : Fin 19, 27 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block28 :
    ∀ c : Fin 55, test55_11 28 c.val = true →
      ∃ i : Fin 19, 28 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block29 :
    ∀ c : Fin 55, test55_11 29 c.val = true →
      ∃ i : Fin 19, 29 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block30 :
    ∀ c : Fin 55, test55_11 30 c.val = true →
      ∃ i : Fin 19, 30 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block31 :
    ∀ c : Fin 55, test55_11 31 c.val = true →
      ∃ i : Fin 19, 31 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block32 :
    ∀ c : Fin 55, test55_11 32 c.val = true →
      ∃ i : Fin 19, 32 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block33 :
    ∀ c : Fin 55, test55_11 33 c.val = true →
      ∃ i : Fin 19, 33 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block34 :
    ∀ c : Fin 55, test55_11 34 c.val = true →
      ∃ i : Fin 19, 34 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block35 :
    ∀ c : Fin 55, test55_11 35 c.val = true →
      ∃ i : Fin 19, 35 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block36 :
    ∀ c : Fin 55, test55_11 36 c.val = true →
      ∃ i : Fin 19, 36 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block37 :
    ∀ c : Fin 55, test55_11 37 c.val = true →
      ∃ i : Fin 19, 37 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block38 :
    ∀ c : Fin 55, test55_11 38 c.val = true →
      ∃ i : Fin 19, 38 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block39 :
    ∀ c : Fin 55, test55_11 39 c.val = true →
      ∃ i : Fin 19, 39 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block40 :
    ∀ c : Fin 55, test55_11 40 c.val = true →
      ∃ i : Fin 19, 40 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block41 :
    ∀ c : Fin 55, test55_11 41 c.val = true →
      ∃ i : Fin 19, 41 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block42 :
    ∀ c : Fin 55, test55_11 42 c.val = true →
      ∃ i : Fin 19, 42 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block43 :
    ∀ c : Fin 55, test55_11 43 c.val = true →
      ∃ i : Fin 19, 43 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block44 :
    ∀ c : Fin 55, test55_11 44 c.val = true →
      ∃ i : Fin 19, 44 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block45 :
    ∀ c : Fin 55, test55_11 45 c.val = true →
      ∃ i : Fin 19, 45 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block46 :
    ∀ c : Fin 55, test55_11 46 c.val = true →
      ∃ i : Fin 19, 46 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block47 :
    ∀ c : Fin 55, test55_11 47 c.val = true →
      ∃ i : Fin 19, 47 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block48 :
    ∀ c : Fin 55, test55_11 48 c.val = true →
      ∃ i : Fin 19, 48 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block49 :
    ∀ c : Fin 55, test55_11 49 c.val = true →
      ∃ i : Fin 19, 49 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block50 :
    ∀ c : Fin 55, test55_11 50 c.val = true →
      ∃ i : Fin 19, 50 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block51 :
    ∀ c : Fin 55, test55_11 51 c.val = true →
      ∃ i : Fin 19, 51 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block52 :
    ∀ c : Fin 55, test55_11 52 c.val = true →
      ∃ i : Fin 19, 52 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block53 :
    ∀ c : Fin 55, test55_11 53 c.val = true →
      ∃ i : Fin 19, 53 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def classify55_11_block54 :
    ∀ c : Fin 55, test55_11 54 c.val = true →
      ∃ i : Fin 19, 54 = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem classify55_11 (b : Fin 55) :
    ∀ c : Fin 55, test55_11 b.val c.val = true →
      ∃ i : Fin 19, b.val = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  fin_cases b
  · simpa using classify55_11_block0
  · simpa using classify55_11_block1
  · simpa using classify55_11_block2
  · simpa using classify55_11_block3
  · simpa using classify55_11_block4
  · simpa using classify55_11_block5
  · simpa using classify55_11_block6
  · simpa using classify55_11_block7
  · simpa using classify55_11_block8
  · simpa using classify55_11_block9
  · simpa using classify55_11_block10
  · simpa using classify55_11_block11
  · simpa using classify55_11_block12
  · simpa using classify55_11_block13
  · simpa using classify55_11_block14
  · simpa using classify55_11_block15
  · simpa using classify55_11_block16
  · simpa using classify55_11_block17
  · simpa using classify55_11_block18
  · simpa using classify55_11_block19
  · simpa using classify55_11_block20
  · simpa using classify55_11_block21
  · simpa using classify55_11_block22
  · simpa using classify55_11_block23
  · simpa using classify55_11_block24
  · simpa using classify55_11_block25
  · simpa using classify55_11_block26
  · simpa using classify55_11_block27
  · simpa using classify55_11_block28
  · simpa using classify55_11_block29
  · simpa using classify55_11_block30
  · simpa using classify55_11_block31
  · simpa using classify55_11_block32
  · simpa using classify55_11_block33
  · simpa using classify55_11_block34
  · simpa using classify55_11_block35
  · simpa using classify55_11_block36
  · simpa using classify55_11_block37
  · simpa using classify55_11_block38
  · simpa using classify55_11_block39
  · simpa using classify55_11_block40
  · simpa using classify55_11_block41
  · simpa using classify55_11_block42
  · simpa using classify55_11_block43
  · simpa using classify55_11_block44
  · simpa using classify55_11_block45
  · simpa using classify55_11_block46
  · simpa using classify55_11_block47
  · simpa using classify55_11_block48
  · simpa using classify55_11_block49
  · simpa using classify55_11_block50
  · simpa using classify55_11_block51
  · simpa using classify55_11_block52
  · simpa using classify55_11_block53
  · simpa using classify55_11_block54

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block0 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block1 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block2 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block3 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block4 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block5 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block6 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block7 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block8 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1_block9 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 39)] [(11, 39), (11, 48)] := by decide
  have ht3 : test55_3 48 39 1 e.val =
      test55_3 39 48 1 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 39 1 d.val e.val =
      test55 q 39 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a1_block0 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1_block10 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 40)] [(11, 40), (11, 48)] := by decide
  have ht3 : test55_3 48 40 1 e.val =
      test55_3 40 48 1 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 40 1 d.val e.val =
      test55 q 40 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a1_block1 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1_block11 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 41)] [(11, 41), (11, 48)] := by decide
  have ht3 : test55_3 48 41 1 e.val =
      test55_3 41 48 1 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 41 1 d.val e.val =
      test55 q 41 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a1_block2 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1_block12 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 42)] [(11, 42), (11, 48)] := by decide
  have ht3 : test55_3 48 42 1 e.val =
      test55_3 42 48 1 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 42 1 d.val e.val =
      test55 q 42 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a1_block3 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1_block13 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 43)] [(11, 43), (11, 48)] := by decide
  have ht3 : test55_3 48 43 1 e.val =
      test55_3 43 48 1 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 43 1 d.val e.val =
      test55 q 43 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a1_block4 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1_block14 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 44)] [(11, 44), (11, 48)] := by decide
  have ht3 : test55_3 48 44 1 e.val =
      test55_3 44 48 1 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 44 1 d.val e.val =
      test55 q 44 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a1_block5 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1_block15 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 45)] [(11, 45), (11, 48)] := by decide
  have ht3 : test55_3 48 45 1 e.val =
      test55_3 45 48 1 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 45 1 d.val e.val =
      test55 q 45 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a1_block6 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1_block16 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 46)] [(11, 46), (11, 48)] := by decide
  have ht3 : test55_3 48 46 1 e.val =
      test55_3 46 48 1 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 46 1 d.val e.val =
      test55 q 46 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a1_block7 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1_block17 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 47)] [(11, 47), (11, 48)] := by decide
  have ht3 : test55_3 48 47 1 e.val =
      test55_3 47 48 1 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 47 1 d.val e.val =
      test55 q 47 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a1_block8 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a1_block18 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a1 (i : Fin 19) :
    ∀ e : Fin 55,
      test55_3 (forms55_11 i).1 (forms55_11 i).2 1 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 i).1 (forms55_11 i).2 1 d.val e.val = true →
      test55 17 (forms55_11 i).1 (forms55_11 i).2 1 d.val e.val = true →
      False := by
  fin_cases i
  · simpa using exclude55_a1_block0
  · simpa using exclude55_a1_block1
  · simpa using exclude55_a1_block2
  · simpa using exclude55_a1_block3
  · simpa using exclude55_a1_block4
  · simpa using exclude55_a1_block5
  · simpa using exclude55_a1_block6
  · simpa using exclude55_a1_block7
  · simpa using exclude55_a1_block8
  · simpa using exclude55_a1_block9
  · simpa using exclude55_a1_block10
  · simpa using exclude55_a1_block11
  · simpa using exclude55_a1_block12
  · simpa using exclude55_a1_block13
  · simpa using exclude55_a1_block14
  · simpa using exclude55_a1_block15
  · simpa using exclude55_a1_block16
  · simpa using exclude55_a1_block17
  · simpa using exclude55_a1_block18

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block0 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block1 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block2 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block3 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block4 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block5 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block6 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block7 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block8 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54_block9 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 39)] [(11, 39), (11, 48)] := by decide
  have ht3 : test55_3 48 39 54 e.val =
      test55_3 39 48 54 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 39 54 d.val e.val =
      test55 q 39 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a54_block0 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54_block10 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 40)] [(11, 40), (11, 48)] := by decide
  have ht3 : test55_3 48 40 54 e.val =
      test55_3 40 48 54 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 40 54 d.val e.val =
      test55 q 40 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a54_block1 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54_block11 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 41)] [(11, 41), (11, 48)] := by decide
  have ht3 : test55_3 48 41 54 e.val =
      test55_3 41 48 54 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 41 54 d.val e.val =
      test55 q 41 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a54_block2 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54_block12 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 42)] [(11, 42), (11, 48)] := by decide
  have ht3 : test55_3 48 42 54 e.val =
      test55_3 42 48 54 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 42 54 d.val e.val =
      test55 q 42 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a54_block3 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54_block13 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 43)] [(11, 43), (11, 48)] := by decide
  have ht3 : test55_3 48 43 54 e.val =
      test55_3 43 48 54 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 43 54 d.val e.val =
      test55 q 43 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a54_block4 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54_block14 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 44)] [(11, 44), (11, 48)] := by decide
  have ht3 : test55_3 48 44 54 e.val =
      test55_3 44 48 54 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 44 54 d.val e.val =
      test55 q 44 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a54_block5 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54_block15 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 45)] [(11, 45), (11, 48)] := by decide
  have ht3 : test55_3 48 45 54 e.val =
      test55_3 45 48 54 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 45 54 d.val e.val =
      test55 q 45 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a54_block6 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54_block16 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 46)] [(11, 46), (11, 48)] := by decide
  have ht3 : test55_3 48 46 54 e.val =
      test55_3 46 48 54 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 46 54 d.val e.val =
      test55 q 46 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a54_block7 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54_block17 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro e h3 d h13 h17
  have hperm : List.Perm [(11, 48), (11, 47)] [(11, 47), (11, 48)] := by decide
  have ht3 : test55_3 48 47 54 e.val =
      test55_3 47 48 54 e.val :=
    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (48912491, e.val)] hperm))
  have htest (q : Nat) : test55 q 48 47 54 d.val e.val =
      test55 q 47 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      hperm))
  exact exclude55_a54_block8 e (ht3.symm.trans h3) d
    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private def exclude55_a54_block18 :
    ∀ e : Fin 55,
      test55_3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem exclude55_a54 (i : Fin 19) :
    ∀ e : Fin 55,
      test55_3 (forms55_11 i).1 (forms55_11 i).2 54 e.val = true →
      ∀ d : Fin 55,
      test55 13 (forms55_11 i).1 (forms55_11 i).2 54 d.val e.val = true →
      test55 17 (forms55_11 i).1 (forms55_11 i).2 54 d.val e.val = true →
      False := by
  fin_cases i
  · simpa using exclude55_a54_block0
  · simpa using exclude55_a54_block1
  · simpa using exclude55_a54_block2
  · simpa using exclude55_a54_block3
  · simpa using exclude55_a54_block4
  · simpa using exclude55_a54_block5
  · simpa using exclude55_a54_block6
  · simpa using exclude55_a54_block7
  · simpa using exclude55_a54_block8
  · simpa using exclude55_a54_block9
  · simpa using exclude55_a54_block10
  · simpa using exclude55_a54_block11
  · simpa using exclude55_a54_block12
  · simpa using exclude55_a54_block13
  · simpa using exclude55_a54_block14
  · simpa using exclude55_a54_block15
  · simpa using exclude55_a54_block16
  · simpa using exclude55_a54_block17
  · simpa using exclude55_a54_block18

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem exclude55 (b c a d e : Fin 55)
    (h5 : test55_5 a.val = true)
    (h11 : test55_11 b.val c.val = true)
    (h3 : test55 3 b.val c.val a.val d.val e.val = true)
    (h13 : test55 13 b.val c.val a.val d.val e.val = true)
    (h17 : test55 17 b.val c.val a.val d.val e.val = true) : False := by
  have h3' : test55_3 b.val c.val a.val e.val = true :=
    (test55_neutral b.val c.val a.val d.val e.val).symm.trans h3
  obtain ⟨i, hb, hc⟩ := classify55_11 b c h11
  rcases classify55_5 a h5 with ha | ha
  · exact exclude55_a1 i e
      (by simpa only [hb, hc, ha] using h3') d
      (by simpa only [hb, hc, ha] using h13)
      (by simpa only [hb, hc, ha] using h17)
  · exact exclude55_a54 i e
      (by simpa only [hb, hc, ha] using h3') d
      (by simpa only [hb, hc, ha] using h13)
      (by simpa only [hb, hc, ha] using h17)

end A245211New

/-!
# The remaining odd squarefree counts below 65 for A245211

This module proves exactly the accepted reduction's H2. It combines the
prime-cycle construction, allocation and rotation of prime tokens, sound
modular checks, and kernel-checked finite exclusions. It makes no claim
about the other hypotheses of the original conjecture's reduction.
-/

namespace A245211New

abbrev RemainingCount (r : Nat) : Prop :=
  r = 15 ∨ r = 21 ∨ r = 33 ∨ r = 35 ∨ r = 39 ∨
    r = 45 ∨ r = 51 ∨ r = 55 ∨ r = 57 ∨ r = 63

/- A finite arithmetic classification, including explicit prime-power
witnesses for every excluded odd count. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem countTable :
    ∀ r : Fin 65, 3 ≤ r.val → Odd r.val →
      RemainingCount r.val ∨
      ∃ (q : Fin 65) (k : Fin 7),
        q.val.Prime ∧ 0 < k.val ∧ r.val = q.val ^ k.val := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem possible_counts (r : Nat) (h3 : 3 ≤ r) (h65 : r < 65)
    (hodd : Odd r)
    (hnp : ∀ q k : Nat, q.Prime → 0 < k → r ≠ q ^ k) :
    RemainingCount r := by
  rcases countTable ⟨r, h65⟩ h3 hodd with h | ⟨q, k, hq, hk, heq⟩
  · exact h
  · exact False.elim (hnp q.val k.val hq hk heq)
abbrev factors15 : List Nat := [3, 3, 11, 331]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count15 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 15) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors15, Nat.Prime q := by
    norm_num [factors15]
  have hfactor : factors15.prod = 2 ^ 15 + 1 := by
    norm_num [factors15]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors15 hprime hfactor (0 : Fin 4)
  have hlarge (i : Fin 15) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (15 - 1)) (hp i).2
  have hspec : tokenSpec factors15 pos = [(3, 0), (3, (pos 1).val), (11, (pos 2).val), (331, (pos 3).val)] := by
    simp [tokenSpec, factors15, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 15 q (projectedTokenSpec q factors15 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors15 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude15 (pos 1) (pos 2)
  simpa [test15, projectedTokenSpec, hspec] using
    hprojected 33 (by decide) (by decide) (by decide)
abbrev factors21 : List Nat := [3, 3, 43, 5419]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count21 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 21) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors21, Nat.Prime q := by
    norm_num [factors21]
  have hfactor : factors21.prod = 2 ^ 21 + 1 := by
    norm_num [factors21]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors21 hprime hfactor (0 : Fin 4)
  have hlarge (i : Fin 21) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (21 - 1)) (hp i).2
  have hspec : tokenSpec factors21 pos = [(3, 0), (3, (pos 1).val), (43, (pos 2).val), (5419, (pos 3).val)] := by
    simp [tokenSpec, factors21, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 21 q (projectedTokenSpec q factors21 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors21 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude21 (pos 1)
  simpa [test21, projectedTokenSpec, hspec] using
    hprojected 3 (by decide) (by decide) (by decide)
abbrev factors33 : List Nat := [3, 3, 67, 683, 20857]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count33 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 33) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors33, Nat.Prime q := by
    norm_num [factors33]
  have hfactor : factors33.prod = 2 ^ 33 + 1 := by
    norm_num [factors33]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors33 hprime hfactor (0 : Fin 5)
  have hlarge (i : Fin 33) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (33 - 1)) (hp i).2
  have hspec : tokenSpec factors33 pos = [(3, 0), (3, (pos 1).val), (67, (pos 2).val), (683, (pos 3).val), (20857, (pos 4).val)] := by
    simp [tokenSpec, factors33, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 33 q (projectedTokenSpec q factors33 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors33 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude33 (pos 1) (pos 3)
  simpa [test33, projectedTokenSpec, hspec] using
    hprojected 33 (by decide) (by decide) (by decide)
abbrev factors35 : List Nat := [3, 11, 43, 281, 86171]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count35 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 35) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors35, Nat.Prime q := by
    norm_num [factors35]
  have hfactor : factors35.prod = 2 ^ 35 + 1 := by
    norm_num [factors35]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors35 hprime hfactor (0 : Fin 5)
  have hlarge (i : Fin 35) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (35 - 1)) (hp i).2
  have hspec : tokenSpec factors35 pos = [(3, 0), (11, (pos 1).val), (43, (pos 2).val), (281, (pos 3).val), (86171, (pos 4).val)] := by
    simp [tokenSpec, factors35, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 35 q (projectedTokenSpec q factors35 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors35 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  have hfull (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 35 q (tokenSpec factors35 pos) = true :=
    positionTest_of_token_cycle (by decide) q hq ho factors35 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude35 (pos 1) (pos 2) (pos 3) (pos 4)
  · simpa [test35_5, projectedTokenSpec, hspec] using
      hprojected 5 (by decide) (by decide) (by decide)
  · simpa [test35_3, projectedTokenSpec, hspec] using
      hprojected 3 (by decide) (by decide) (by decide)
  · simpa only [test35, hspec] using
      hfull 7 (by decide) (by decide) (by decide)
  · simpa only [test35, hspec] using
      hfull 11 (by decide) (by decide) (by decide)
  · simpa only [test35, hspec] using
      hfull 13 (by decide) (by decide) (by decide)

abbrev factors39 : List Nat := [3, 3, 2731, 22366891]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count39 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 39) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors39, Nat.Prime q := by
    norm_num [factors39]
  have hfactor : factors39.prod = 2 ^ 39 + 1 := by
    norm_num [factors39]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors39 hprime hfactor (0 : Fin 4)
  have hlarge (i : Fin 39) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (39 - 1)) (hp i).2
  have hspec : tokenSpec factors39 pos = [(3, 0), (3, (pos 1).val), (2731, (pos 2).val), (22366891, (pos 3).val)] := by
    simp [tokenSpec, factors39, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 39 q (projectedTokenSpec q factors39 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors39 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude39 (pos 1)
  simpa [test39, projectedTokenSpec, hspec] using
    hprojected 3 (by decide) (by decide) (by decide)
abbrev factors45 : List Nat := [3, 3, 3, 11, 19, 331, 18837001]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count45 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 45) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors45, Nat.Prime q := by
    norm_num [factors45]
  have hfactor : factors45.prod = 2 ^ 45 + 1 := by
    norm_num [factors45]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors45 hprime hfactor (3 : Fin 7)
  have hlarge (i : Fin 45) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (45 - 1)) (hp i).2
  have hspec : tokenSpec factors45 pos = [(3, (pos 0).val), (3, (pos 1).val), (3, (pos 2).val), (11, 0), (19, (pos 4).val), (331, (pos 5).val), (18837001, (pos 6).val)] := by
    simp [tokenSpec, factors45, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 45 q (projectedTokenSpec q factors45 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors45 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  have hfull (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 45 q (tokenSpec factors45 pos) = true :=
    positionTest_of_token_cycle (by decide) q hq ho factors45 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude45 (pos 0) (pos 1) (pos 2) (pos 4) (pos 5) (pos 6)
  · simpa [test45_3, projectedTokenSpec, hspec] using
      hprojected 3 (by decide) (by decide) (by decide)
  · change positionTest 45 5 [(3, (pos 0).val), (3, (pos 1).val), (3, (pos 2).val), (11, 0), (19, (pos 4).val)] = true
    rw [← positionTest_filter_ne_one 45 5 (by decide) [(3, (pos 0).val), (3, (pos 1).val), (3, (pos 2).val), (11, 0), (19, (pos 4).val)]]
    simpa [projectedTokenSpec, hspec] using
      hprojected 5 (by decide) (by decide) (by decide)
  · simpa only [test45, hspec] using
      hfull 7 (by decide) (by decide) (by decide)
  · simpa only [test45, hspec] using
      hfull 13 (by decide) (by decide) (by decide)
  · simpa only [test45, hspec] using
      hfull 19 (by decide) (by decide) (by decide)

abbrev factors51 : List Nat := [3, 3, 307, 2857, 6529, 43691]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count51 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 51) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors51, Nat.Prime q := by
    norm_num [factors51]
  have hfactor : factors51.prod = 2 ^ 51 + 1 := by
    norm_num [factors51]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors51 hprime hfactor (5 : Fin 6)
  have hlarge (i : Fin 51) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (51 - 1)) (hp i).2
  have hspec : tokenSpec factors51 pos = [(3, (pos 0).val), (3, (pos 1).val), (307, (pos 2).val), (2857, (pos 3).val), (6529, (pos 4).val), (43691, 0)] := by
    simp [tokenSpec, factors51, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 51 q (projectedTokenSpec q factors51 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors51 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  have hfull (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 51 q (tokenSpec factors51 pos) = true :=
    positionTest_of_token_cycle (by decide) q hq ho factors51 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude51 (pos 0) (pos 1) (pos 2) (pos 3) (pos 4)
  · simpa [test51_3, projectedTokenSpec, hspec] using
      hprojected 3 (by decide) (by decide) (by decide)
  · simpa [test51_7, projectedTokenSpec, hspec] using
      hprojected 7 (by decide) (by decide) (by decide)
  · simpa only [test51, hspec] using
      hfull 5 (by decide) (by decide) (by decide)
  · simpa only [test51, hspec] using
      hfull 11 (by decide) (by decide) (by decide)
  · simpa only [test51, hspec] using
      hfull 13 (by decide) (by decide) (by decide)

abbrev factors55 : List Nat := [3, 11, 11, 683, 2971, 48912491]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count55 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 55) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors55, Nat.Prime q := by
    norm_num [factors55]
  have hfactor : factors55.prod = 2 ^ 55 + 1 := by
    norm_num [factors55]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors55 hprime hfactor (0 : Fin 6)
  have hlarge (i : Fin 55) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (55 - 1)) (hp i).2
  have hspec : tokenSpec factors55 pos = [(3, 0), (11, (pos 1).val), (11, (pos 2).val), (683, (pos 3).val), (2971, (pos 4).val), (48912491, (pos 5).val)] := by
    simp [tokenSpec, factors55, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 55 q (projectedTokenSpec q factors55 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors55 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  have hfull (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 55 q (tokenSpec factors55 pos) = true :=
    positionTest_of_token_cycle (by decide) q hq ho factors55 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude55 (pos 1) (pos 2) (pos 3) (pos 4) (pos 5)
  · simpa [test55_5, projectedTokenSpec, hspec] using
      hprojected 5 (by decide) (by decide) (by decide)
  · simpa [test55_11, projectedTokenSpec, hspec] using
      hprojected 11 (by decide) (by decide) (by decide)
  · simpa only [test55, hspec] using
      hfull 3 (by decide) (by decide) (by decide)
  · simpa only [test55, hspec] using
      hfull 13 (by decide) (by decide) (by decide)
  · simpa only [test55, hspec] using
      hfull 17 (by decide) (by decide) (by decide)

abbrev factors57 : List Nat := [3, 3, 571, 174763, 160465489]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count57 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 57) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors57, Nat.Prime q := by
    norm_num [factors57]
  have hfactor : factors57.prod = 2 ^ 57 + 1 := by
    norm_num [factors57]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors57 hprime hfactor (0 : Fin 5)
  have hlarge (i : Fin 57) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (57 - 1)) (hp i).2
  have hspec : tokenSpec factors57 pos = [(3, 0), (3, (pos 1).val), (571, (pos 2).val), (174763, (pos 3).val), (160465489, (pos 4).val)] := by
    simp [tokenSpec, factors57, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 57 q (projectedTokenSpec q factors57 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors57 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude57 (pos 1)
  simpa [test57, projectedTokenSpec, hspec] using
    hprojected 3 (by decide) (by decide) (by decide)
abbrev factors63 : List Nat := [3, 3, 3, 19, 43, 5419, 77158673929]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem no_fixed_count63 {n : Nat} (hs : Squarefree n)
    (hr : n.primeFactors.card = 63) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors63, Nat.Prime q := by
    norm_num [factors63]
  have hfactor : factors63.prod = 2 ^ 63 + 1 := by
    norm_num [factors63]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors63 hprime hfactor (0 : Fin 7)
  have hlarge (i : Fin 63) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ (63 - 1)) (hp i).2
  have hspec : tokenSpec factors63 pos = [(3, 0), (3, (pos 1).val), (3, (pos 2).val), (19, (pos 3).val), (43, (pos 4).val), (5419, (pos 5).val), (77158673929, (pos 6).val)] := by
    simp [tokenSpec, factors63, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest 63 q (projectedTokenSpec q factors63 pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors63 pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))
  apply exclude63 (pos 1) (pos 2)
  simpa [test63, projectedTokenSpec, hspec] using
    hprojected 3 (by decide) (by decide) (by decide)
end A245211New

/- The exact second hypothesis of the accepted R2 reduction. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem OMA.solution : OMA.R_OeisA245211_conjecture_R2.H2 := by
  intro n hs h3 h65 hodd hnp ha
  have hr := A245211New.possible_counts n.primeFactors.card h3 h65 hodd hnp
  rcases hr with h15 | h21 | h33 | h35 | h39 | h45 | h51 | h55 | h57 | h63
  · exact A245211New.no_fixed_count15 hs h15 ha
  · exact A245211New.no_fixed_count21 hs h21 ha
  · exact A245211New.no_fixed_count33 hs h33 ha
  · exact A245211New.no_fixed_count35 hs h35 ha
  · exact A245211New.no_fixed_count39 hs h39 ha
  · exact A245211New.no_fixed_count45 hs h45 ha
  · exact A245211New.no_fixed_count51 hs h51 ha
  · exact A245211New.no_fixed_count55 hs h55 ha
  · exact A245211New.no_fixed_count57 hs h57 ha
  · exact A245211New.no_fixed_count63 hs h63 ha
