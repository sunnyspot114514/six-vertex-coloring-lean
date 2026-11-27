import OMAReductions.R_OeisA245211_conjecture_R2
import Mathlib.Dynamics.PeriodicPts.Lemmas

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
