import A245211.Projection
import A245211.Finite

/-!
# The remaining odd squarefree counts below 65 for A245211

This module proves exactly the accepted reduction's H2. It combines the
prime-cycle construction, allocation and rotation of prime tokens, sound
modular checks, and kernel-checked finite exclusions. It makes no claim
about the other hypotheses of the original conjecture's reduction.
-/

namespace A245211New

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev RemainingCount (r : Nat) : Prop :=
  r = 15 ∨ r = 21 ∨ r = 33 ∨ r = 35 ∨ r = 39 ∨
    r = 45 ∨ r = 51 ∨ r = 55 ∨ r = 57 ∨ r = 63

/-- A finite arithmetic classification, including explicit prime-power
witnesses for every excluded odd count. -/
private theorem countTable :
    ∀ r : Fin 65, 3 ≤ r.val → Odd r.val →
      RemainingCount r.val ∨
      ∃ (q : Fin 65) (k : Fin 7),
        q.val.Prime ∧ 0 < k.val ∧ r.val = q.val ^ k.val := by
  decide +kernel

theorem possible_counts (r : Nat) (h3 : 3 ≤ r) (h65 : r < 65)
    (hodd : Odd r)
    (hnp : ∀ q k : Nat, q.Prime → 0 < k → r ≠ q ^ k) :
    RemainingCount r := by
  rcases countTable ⟨r, h65⟩ h3 hodd with h | ⟨q, k, hq, hk, heq⟩
  · exact h
  · exact False.elim (hnp q.val k.val hq hk heq)
abbrev factors15 : List Nat := [3, 3, 11, 331]
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

/-- The exact second hypothesis of the accepted R2 reduction. -/
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

