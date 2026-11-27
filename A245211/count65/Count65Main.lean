import A245211.Projection

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
