import A245211.Cycle
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

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
