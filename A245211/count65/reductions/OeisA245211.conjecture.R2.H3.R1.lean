import OMAReductions.R_OeisA245211_conjecture_R2

/-!
# Separate the 65-factor boundary case from the remaining large counts

The boundary case is stated without a bound on the integer itself.
After excluding it, oddness raises the remaining factor-count bound to 67.
-/

namespace OMA.R_OeisA245211_conjecture_R2_H3_R1

/-- The first remaining squarefree count has no fixed point. -/
def H1 : Prop :=
  ∀ n : ℕ, Squarefree n → n.primeFactors.card = 65 →
    OeisA245211.a n ≠ n

/-- The remaining odd counts are at least 67 and are not prime powers. -/
def H2 : Prop :=
  ∀ n : ℕ, Squarefree n → 67 ≤ n.primeFactors.card →
    Odd n.primeFactors.card →
    (∀ q k : ℕ, q.Prime → 0 < k → n.primeFactors.card ≠ q ^ k) →
    OeisA245211.a n ≠ n

theorem main : H1 → H2 → OMA.R_OeisA245211_conjecture_R2.H3 := by
  intro h1 h2 n hs h65 hodd hnp
  by_cases heq : n.primeFactors.card = 65
  · exact h1 n hs heq
  · apply h2 n hs ?_ hodd hnp
    obtain ⟨k, hk⟩ := hodd
    omega

end OMA.R_OeisA245211_conjecture_R2_H3_R1
