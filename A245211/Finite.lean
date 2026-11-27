import A245211.Core

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

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-! ## Six small cases -/
abbrev test15 (a b : Nat) : Bool :=
  positionTest 15 33 [(3, 0), (3, a), (11, b)]
theorem exclude15 :
    ∀ a b : Fin 15, test15 a.val b.val = true → False := by
  decide +kernel
abbrev test21 (a : Nat) : Bool :=
  positionTest 21 3 [(3, 0), (3, a)]
theorem exclude21 :
    ∀ a : Fin 21, test21 a.val = true → False := by
  decide +kernel
abbrev test33 (a b : Nat) : Bool :=
  positionTest 33 33 [(3, 0), (3, a), (683, b)]
theorem exclude33 :
    ∀ a b : Fin 33, test33 a.val b.val = true → False := by
  decide +kernel
abbrev test39 (a : Nat) : Bool :=
  positionTest 39 3 [(3, 0), (3, a)]
theorem exclude39 :
    ∀ a : Fin 39, test39 a.val = true → False := by
  decide +kernel
abbrev test57 (a : Nat) : Bool :=
  positionTest 57 3 [(3, 0), (3, a)]
theorem exclude57 :
    ∀ a : Fin 57, test57 a.val = true → False := by
  decide +kernel
abbrev test63 (a b : Nat) : Bool :=
  positionTest 63 3 [(3, 0), (3, a), (3, b)]
theorem exclude63 :
    ∀ a b : Fin 63, test63 a.val b.val = true → False := by
  decide +kernel
/-! ## Thirty-five factors -/
abbrev test35_5 (a : Nat) : Bool :=
  positionTest 35 5 [(3, 0), (43, a)]
abbrev test35_3 (b c d : Nat) : Bool :=
  positionTest 35 3 [(3, 0), (11, b), (281, c), (86171, d)]
abbrev test35 (q b a c d : Nat) : Bool :=
  positionTest 35 q [(3, 0), (11, b), (43, a), (281, c), (86171, d)]
private theorem classify35_5 :
    ∀ a : Fin 35, test35_5 a.val = true → a.val = 1 ∨ a.val = 34 := by
  decide +kernel
private theorem classify35_3_block0 :
    ∀ c d : Fin 35, test35_3 0 c.val d.val = true →
      (0 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 0 = d.val) ∨ (d.val = 1 ∧ 0 = c.val) := by
  decide +kernel
private theorem classify35_3_block1 :
    ∀ c d : Fin 35, test35_3 1 c.val d.val = true →
      (1 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 1 = d.val) ∨ (d.val = 1 ∧ 1 = c.val) := by
  decide +kernel
private theorem classify35_3_block2 :
    ∀ c d : Fin 35, test35_3 2 c.val d.val = true →
      (2 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 2 = d.val) ∨ (d.val = 1 ∧ 2 = c.val) := by
  decide +kernel
private theorem classify35_3_block3 :
    ∀ c d : Fin 35, test35_3 3 c.val d.val = true →
      (3 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 3 = d.val) ∨ (d.val = 1 ∧ 3 = c.val) := by
  decide +kernel
private theorem classify35_3_block4 :
    ∀ c d : Fin 35, test35_3 4 c.val d.val = true →
      (4 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 4 = d.val) ∨ (d.val = 1 ∧ 4 = c.val) := by
  decide +kernel
private theorem classify35_3_block5 :
    ∀ c d : Fin 35, test35_3 5 c.val d.val = true →
      (5 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 5 = d.val) ∨ (d.val = 1 ∧ 5 = c.val) := by
  decide +kernel
private theorem classify35_3_block6 :
    ∀ c d : Fin 35, test35_3 6 c.val d.val = true →
      (6 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 6 = d.val) ∨ (d.val = 1 ∧ 6 = c.val) := by
  decide +kernel
private theorem classify35_3_block7 :
    ∀ c d : Fin 35, test35_3 7 c.val d.val = true →
      (7 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 7 = d.val) ∨ (d.val = 1 ∧ 7 = c.val) := by
  decide +kernel
private theorem classify35_3_block8 :
    ∀ c d : Fin 35, test35_3 8 c.val d.val = true →
      (8 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 8 = d.val) ∨ (d.val = 1 ∧ 8 = c.val) := by
  decide +kernel
private theorem classify35_3_block9 :
    ∀ c d : Fin 35, test35_3 9 c.val d.val = true →
      (9 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 9 = d.val) ∨ (d.val = 1 ∧ 9 = c.val) := by
  decide +kernel
private theorem classify35_3_block10 :
    ∀ c d : Fin 35, test35_3 10 c.val d.val = true →
      (10 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 10 = d.val) ∨ (d.val = 1 ∧ 10 = c.val) := by
  decide +kernel
private theorem classify35_3_block11 :
    ∀ c d : Fin 35, test35_3 11 c.val d.val = true →
      (11 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 11 = d.val) ∨ (d.val = 1 ∧ 11 = c.val) := by
  decide +kernel
private theorem classify35_3_block12 :
    ∀ c d : Fin 35, test35_3 12 c.val d.val = true →
      (12 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 12 = d.val) ∨ (d.val = 1 ∧ 12 = c.val) := by
  decide +kernel
private theorem classify35_3_block13 :
    ∀ c d : Fin 35, test35_3 13 c.val d.val = true →
      (13 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 13 = d.val) ∨ (d.val = 1 ∧ 13 = c.val) := by
  decide +kernel
private theorem classify35_3_block14 :
    ∀ c d : Fin 35, test35_3 14 c.val d.val = true →
      (14 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 14 = d.val) ∨ (d.val = 1 ∧ 14 = c.val) := by
  decide +kernel
private theorem classify35_3_block15 :
    ∀ c d : Fin 35, test35_3 15 c.val d.val = true →
      (15 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 15 = d.val) ∨ (d.val = 1 ∧ 15 = c.val) := by
  decide +kernel
private theorem classify35_3_block16 :
    ∀ c d : Fin 35, test35_3 16 c.val d.val = true →
      (16 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 16 = d.val) ∨ (d.val = 1 ∧ 16 = c.val) := by
  decide +kernel
private theorem classify35_3_block17 :
    ∀ c d : Fin 35, test35_3 17 c.val d.val = true →
      (17 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 17 = d.val) ∨ (d.val = 1 ∧ 17 = c.val) := by
  decide +kernel
private theorem classify35_3_block18 :
    ∀ c d : Fin 35, test35_3 18 c.val d.val = true →
      (18 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 18 = d.val) ∨ (d.val = 1 ∧ 18 = c.val) := by
  decide +kernel
private theorem classify35_3_block19 :
    ∀ c d : Fin 35, test35_3 19 c.val d.val = true →
      (19 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 19 = d.val) ∨ (d.val = 1 ∧ 19 = c.val) := by
  decide +kernel
private theorem classify35_3_block20 :
    ∀ c d : Fin 35, test35_3 20 c.val d.val = true →
      (20 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 20 = d.val) ∨ (d.val = 1 ∧ 20 = c.val) := by
  decide +kernel
private theorem classify35_3_block21 :
    ∀ c d : Fin 35, test35_3 21 c.val d.val = true →
      (21 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 21 = d.val) ∨ (d.val = 1 ∧ 21 = c.val) := by
  decide +kernel
private theorem classify35_3_block22 :
    ∀ c d : Fin 35, test35_3 22 c.val d.val = true →
      (22 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 22 = d.val) ∨ (d.val = 1 ∧ 22 = c.val) := by
  decide +kernel
private theorem classify35_3_block23 :
    ∀ c d : Fin 35, test35_3 23 c.val d.val = true →
      (23 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 23 = d.val) ∨ (d.val = 1 ∧ 23 = c.val) := by
  decide +kernel
private theorem classify35_3_block24 :
    ∀ c d : Fin 35, test35_3 24 c.val d.val = true →
      (24 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 24 = d.val) ∨ (d.val = 1 ∧ 24 = c.val) := by
  decide +kernel
private theorem classify35_3_block25 :
    ∀ c d : Fin 35, test35_3 25 c.val d.val = true →
      (25 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 25 = d.val) ∨ (d.val = 1 ∧ 25 = c.val) := by
  decide +kernel
private theorem classify35_3_block26 :
    ∀ c d : Fin 35, test35_3 26 c.val d.val = true →
      (26 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 26 = d.val) ∨ (d.val = 1 ∧ 26 = c.val) := by
  decide +kernel
private theorem classify35_3_block27 :
    ∀ c d : Fin 35, test35_3 27 c.val d.val = true →
      (27 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 27 = d.val) ∨ (d.val = 1 ∧ 27 = c.val) := by
  decide +kernel
private theorem classify35_3_block28 :
    ∀ c d : Fin 35, test35_3 28 c.val d.val = true →
      (28 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 28 = d.val) ∨ (d.val = 1 ∧ 28 = c.val) := by
  decide +kernel
private theorem classify35_3_block29 :
    ∀ c d : Fin 35, test35_3 29 c.val d.val = true →
      (29 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 29 = d.val) ∨ (d.val = 1 ∧ 29 = c.val) := by
  decide +kernel
private theorem classify35_3_block30 :
    ∀ c d : Fin 35, test35_3 30 c.val d.val = true →
      (30 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 30 = d.val) ∨ (d.val = 1 ∧ 30 = c.val) := by
  decide +kernel
private theorem classify35_3_block31 :
    ∀ c d : Fin 35, test35_3 31 c.val d.val = true →
      (31 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 31 = d.val) ∨ (d.val = 1 ∧ 31 = c.val) := by
  decide +kernel
private theorem classify35_3_block32 :
    ∀ c d : Fin 35, test35_3 32 c.val d.val = true →
      (32 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 32 = d.val) ∨ (d.val = 1 ∧ 32 = c.val) := by
  decide +kernel
private theorem classify35_3_block33 :
    ∀ c d : Fin 35, test35_3 33 c.val d.val = true →
      (33 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 33 = d.val) ∨ (d.val = 1 ∧ 33 = c.val) := by
  decide +kernel
private theorem classify35_3_block34 :
    ∀ c d : Fin 35, test35_3 34 c.val d.val = true →
      (34 = 1 ∧ c.val = d.val) ∨
      (c.val = 1 ∧ 34 = d.val) ∨ (d.val = 1 ∧ 34 = c.val) := by
  decide +kernel
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

private theorem exclude35_pattern0 :
    ∀ a t : Fin 35, (a.val = 1 ∨ a.val = 34) →
      test35 7 1 a.val t.val t.val = true →
      test35 11 1 a.val t.val t.val = true →
      test35 13 1 a.val t.val t.val = true →
      False := by
  decide +kernel
private theorem exclude35_pattern1 :
    ∀ a t : Fin 35, (a.val = 1 ∨ a.val = 34) →
      test35 7 t.val a.val 1 t.val = true →
      test35 11 t.val a.val 1 t.val = true →
      test35 13 t.val a.val 1 t.val = true →
      False := by
  decide +kernel
private theorem exclude35_pattern2 :
    ∀ a t : Fin 35, (a.val = 1 ∨ a.val = 34) →
      test35 7 t.val a.val t.val 1 = true →
      test35 11 t.val a.val t.val 1 = true →
      test35 13 t.val a.val t.val 1 = true →
      False := by
  decide +kernel
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
abbrev test45 (q a b c d e f : Nat) : Bool :=
  positionTest 45 q [(3, a), (3, b), (3, c), (11, 0), (19, d), (331, e), (18837001, f)]
private theorem classify45_3_block0 :
    ∀ b c : Fin 45, test45_3 0 b.val c.val = true →
      ∃ i : Fin 13, 0 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block1 :
    ∀ b c : Fin 45, test45_3 1 b.val c.val = true →
      ∃ i : Fin 13, 1 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block2 :
    ∀ b c : Fin 45, test45_3 2 b.val c.val = true →
      ∃ i : Fin 13, 2 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block3 :
    ∀ b c : Fin 45, test45_3 3 b.val c.val = true →
      ∃ i : Fin 13, 3 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block4 :
    ∀ b c : Fin 45, test45_3 4 b.val c.val = true →
      ∃ i : Fin 13, 4 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block5 :
    ∀ b c : Fin 45, test45_3 5 b.val c.val = true →
      ∃ i : Fin 13, 5 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block6 :
    ∀ b c : Fin 45, test45_3 6 b.val c.val = true →
      ∃ i : Fin 13, 6 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block7 :
    ∀ b c : Fin 45, test45_3 7 b.val c.val = true →
      ∃ i : Fin 13, 7 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block8 :
    ∀ b c : Fin 45, test45_3 8 b.val c.val = true →
      ∃ i : Fin 13, 8 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block9 :
    ∀ b c : Fin 45, test45_3 9 b.val c.val = true →
      ∃ i : Fin 13, 9 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block10 :
    ∀ b c : Fin 45, test45_3 10 b.val c.val = true →
      ∃ i : Fin 13, 10 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block11 :
    ∀ b c : Fin 45, test45_3 11 b.val c.val = true →
      ∃ i : Fin 13, 11 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block12 :
    ∀ b c : Fin 45, test45_3 12 b.val c.val = true →
      ∃ i : Fin 13, 12 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block13 :
    ∀ b c : Fin 45, test45_3 13 b.val c.val = true →
      ∃ i : Fin 13, 13 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block14 :
    ∀ b c : Fin 45, test45_3 14 b.val c.val = true →
      ∃ i : Fin 13, 14 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block15 :
    ∀ b c : Fin 45, test45_3 15 b.val c.val = true →
      ∃ i : Fin 13, 15 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block16 :
    ∀ b c : Fin 45, test45_3 16 b.val c.val = true →
      ∃ i : Fin 13, 16 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block17 :
    ∀ b c : Fin 45, test45_3 17 b.val c.val = true →
      ∃ i : Fin 13, 17 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block18 :
    ∀ b c : Fin 45, test45_3 18 b.val c.val = true →
      ∃ i : Fin 13, 18 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block19 :
    ∀ b c : Fin 45, test45_3 19 b.val c.val = true →
      ∃ i : Fin 13, 19 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block20 :
    ∀ b c : Fin 45, test45_3 20 b.val c.val = true →
      ∃ i : Fin 13, 20 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block21 :
    ∀ b c : Fin 45, test45_3 21 b.val c.val = true →
      ∃ i : Fin 13, 21 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block22 :
    ∀ b c : Fin 45, test45_3 22 b.val c.val = true →
      ∃ i : Fin 13, 22 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block23 :
    ∀ b c : Fin 45, test45_3 23 b.val c.val = true →
      ∃ i : Fin 13, 23 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block24 :
    ∀ b c : Fin 45, test45_3 24 b.val c.val = true →
      ∃ i : Fin 13, 24 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block25 :
    ∀ b c : Fin 45, test45_3 25 b.val c.val = true →
      ∃ i : Fin 13, 25 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block26 :
    ∀ b c : Fin 45, test45_3 26 b.val c.val = true →
      ∃ i : Fin 13, 26 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block27 :
    ∀ b c : Fin 45, test45_3 27 b.val c.val = true →
      ∃ i : Fin 13, 27 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block28 :
    ∀ b c : Fin 45, test45_3 28 b.val c.val = true →
      ∃ i : Fin 13, 28 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block29 :
    ∀ b c : Fin 45, test45_3 29 b.val c.val = true →
      ∃ i : Fin 13, 29 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block30 :
    ∀ b c : Fin 45, test45_3 30 b.val c.val = true →
      ∃ i : Fin 13, 30 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block31 :
    ∀ b c : Fin 45, test45_3 31 b.val c.val = true →
      ∃ i : Fin 13, 31 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block32 :
    ∀ b c : Fin 45, test45_3 32 b.val c.val = true →
      ∃ i : Fin 13, 32 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block33 :
    ∀ b c : Fin 45, test45_3 33 b.val c.val = true →
      ∃ i : Fin 13, 33 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block34 :
    ∀ b c : Fin 45, test45_3 34 b.val c.val = true →
      ∃ i : Fin 13, 34 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block35 :
    ∀ b c : Fin 45, test45_3 35 b.val c.val = true →
      ∃ i : Fin 13, 35 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block36 :
    ∀ b c : Fin 45, test45_3 36 b.val c.val = true →
      ∃ i : Fin 13, 36 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block37 :
    ∀ b c : Fin 45, test45_3 37 b.val c.val = true →
      ∃ i : Fin 13, 37 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block38 :
    ∀ b c : Fin 45, test45_3 38 b.val c.val = true →
      ∃ i : Fin 13, 38 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block39 :
    ∀ b c : Fin 45, test45_3 39 b.val c.val = true →
      ∃ i : Fin 13, 39 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block40 :
    ∀ b c : Fin 45, test45_3 40 b.val c.val = true →
      ∃ i : Fin 13, 40 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block41 :
    ∀ b c : Fin 45, test45_3 41 b.val c.val = true →
      ∃ i : Fin 13, 41 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block42 :
    ∀ b c : Fin 45, test45_3 42 b.val c.val = true →
      ∃ i : Fin 13, 42 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block43 :
    ∀ b c : Fin 45, test45_3 43 b.val c.val = true →
      ∃ i : Fin 13, 43 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
private theorem classify45_3_block44 :
    ∀ b c : Fin 45, test45_3 44 b.val c.val = true →
      ∃ i : Fin 13, 44 = (forms45_3 i).1 ∧
        b.val = (forms45_3 i).2.1 ∧ c.val = (forms45_3 i).2.2 := by
  decide +kernel
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

private theorem classify45_5 :
    ∀ (i : Fin 13) (d : Fin 45),
      test45_5 (forms45_3 i).1 (forms45_3 i).2.1 (forms45_3 i).2.2 d.val = true →
      ∃ j : Fin 13, (forms45_3 i).1 = (forms45_5 j).1 ∧
        (forms45_3 i).2.1 = (forms45_5 j).2.1 ∧
        (forms45_3 i).2.2 = (forms45_5 j).2.2.1 ∧
        d.val = (forms45_5 j).2.2.2 := by
  decide +kernel
private theorem exclude45_forms_block0 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block1 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (1 : Fin 13)).1 (forms45_5 (1 : Fin 13)).2.1 (forms45_5 (1 : Fin 13)).2.2.1 (forms45_5 (1 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (1 : Fin 13)).1 (forms45_5 (1 : Fin 13)).2.1 (forms45_5 (1 : Fin 13)).2.2.1 (forms45_5 (1 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (1 : Fin 13)).1 (forms45_5 (1 : Fin 13)).2.1 (forms45_5 (1 : Fin 13)).2.2.1 (forms45_5 (1 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block2 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (2 : Fin 13)).1 (forms45_5 (2 : Fin 13)).2.1 (forms45_5 (2 : Fin 13)).2.2.1 (forms45_5 (2 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (2 : Fin 13)).1 (forms45_5 (2 : Fin 13)).2.1 (forms45_5 (2 : Fin 13)).2.2.1 (forms45_5 (2 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (2 : Fin 13)).1 (forms45_5 (2 : Fin 13)).2.1 (forms45_5 (2 : Fin 13)).2.2.1 (forms45_5 (2 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block3 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (3 : Fin 13)).1 (forms45_5 (3 : Fin 13)).2.1 (forms45_5 (3 : Fin 13)).2.2.1 (forms45_5 (3 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (3 : Fin 13)).1 (forms45_5 (3 : Fin 13)).2.1 (forms45_5 (3 : Fin 13)).2.2.1 (forms45_5 (3 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (3 : Fin 13)).1 (forms45_5 (3 : Fin 13)).2.1 (forms45_5 (3 : Fin 13)).2.2.1 (forms45_5 (3 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block4 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block5 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block6 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (6 : Fin 13)).1 (forms45_5 (6 : Fin 13)).2.1 (forms45_5 (6 : Fin 13)).2.2.1 (forms45_5 (6 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (6 : Fin 13)).1 (forms45_5 (6 : Fin 13)).2.1 (forms45_5 (6 : Fin 13)).2.2.1 (forms45_5 (6 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (6 : Fin 13)).1 (forms45_5 (6 : Fin 13)).2.1 (forms45_5 (6 : Fin 13)).2.2.1 (forms45_5 (6 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block7 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (7 : Fin 13)).1 (forms45_5 (7 : Fin 13)).2.1 (forms45_5 (7 : Fin 13)).2.2.1 (forms45_5 (7 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (7 : Fin 13)).1 (forms45_5 (7 : Fin 13)).2.1 (forms45_5 (7 : Fin 13)).2.2.1 (forms45_5 (7 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (7 : Fin 13)).1 (forms45_5 (7 : Fin 13)).2.1 (forms45_5 (7 : Fin 13)).2.2.1 (forms45_5 (7 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block8 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (8 : Fin 13)).1 (forms45_5 (8 : Fin 13)).2.1 (forms45_5 (8 : Fin 13)).2.2.1 (forms45_5 (8 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (8 : Fin 13)).1 (forms45_5 (8 : Fin 13)).2.1 (forms45_5 (8 : Fin 13)).2.2.1 (forms45_5 (8 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (8 : Fin 13)).1 (forms45_5 (8 : Fin 13)).2.1 (forms45_5 (8 : Fin 13)).2.2.1 (forms45_5 (8 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block9 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (9 : Fin 13)).1 (forms45_5 (9 : Fin 13)).2.1 (forms45_5 (9 : Fin 13)).2.2.1 (forms45_5 (9 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (9 : Fin 13)).1 (forms45_5 (9 : Fin 13)).2.1 (forms45_5 (9 : Fin 13)).2.2.1 (forms45_5 (9 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (9 : Fin 13)).1 (forms45_5 (9 : Fin 13)).2.1 (forms45_5 (9 : Fin 13)).2.2.1 (forms45_5 (9 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block10 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (10 : Fin 13)).1 (forms45_5 (10 : Fin 13)).2.1 (forms45_5 (10 : Fin 13)).2.2.1 (forms45_5 (10 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (10 : Fin 13)).1 (forms45_5 (10 : Fin 13)).2.1 (forms45_5 (10 : Fin 13)).2.2.1 (forms45_5 (10 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (10 : Fin 13)).1 (forms45_5 (10 : Fin 13)).2.1 (forms45_5 (10 : Fin 13)).2.2.1 (forms45_5 (10 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block11 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (11 : Fin 13)).1 (forms45_5 (11 : Fin 13)).2.1 (forms45_5 (11 : Fin 13)).2.2.1 (forms45_5 (11 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (11 : Fin 13)).1 (forms45_5 (11 : Fin 13)).2.1 (forms45_5 (11 : Fin 13)).2.2.1 (forms45_5 (11 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (11 : Fin 13)).1 (forms45_5 (11 : Fin 13)).2.1 (forms45_5 (11 : Fin 13)).2.2.1 (forms45_5 (11 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block12 :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms (j : Fin 13) :
    ∀ e f : Fin 45,
      test45 7 (forms45_5 j).1 (forms45_5 j).2.1 (forms45_5 j).2.2.1 (forms45_5 j).2.2.2 e.val f.val = true →
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

theorem exclude45 (a b c d e f : Fin 45)
    (h3 : test45_3 a.val b.val c.val = true)
    (h5 : test45_5 a.val b.val c.val d.val = true)
    (h7 : test45 7 a.val b.val c.val d.val e.val f.val = true)
    (h13 : test45 13 a.val b.val c.val d.val e.val f.val = true)
    (h19 : test45 19 a.val b.val c.val d.val e.val f.val = true) : False := by
  obtain ⟨i, ha, hb, hc⟩ := classify45_3 a b c h3
  obtain ⟨j, hja, hjb, hjc, hjd⟩ := classify45_5 i d
    (by simpa only [ha, hb, hc] using h5)
  exact exclude45_forms j e f
    (by simpa only [ha, hb, hc, hja, hjb, hjc, hjd] using h7)
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
private theorem classify51_3 :
    ∀ a b : Fin 51, test51_3 a.val b.val = true →
      ∃ i : Fin 3, a.val = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2 := by
  decide +kernel
private theorem exclude51_forms_block0 :
    ∀ c e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 c.val e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 c.val d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 c.val d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 c.val d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block1 :
    ∀ c e : Fin 51, test51_7 (forms51_3 (1 : Fin 3)).1 (forms51_3 (1 : Fin 3)).2 c.val e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (1 : Fin 3)).1 (forms51_3 (1 : Fin 3)).2 c.val d.val e.val = true →
      test51 11 (forms51_3 (1 : Fin 3)).1 (forms51_3 (1 : Fin 3)).2 c.val d.val e.val = true →
      test51 13 (forms51_3 (1 : Fin 3)).1 (forms51_3 (1 : Fin 3)).2 c.val d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2 :
    ∀ c e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 c.val e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 c.val d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 c.val d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 c.val d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms (i : Fin 3) :
    ∀ c e : Fin 51, test51_7 (forms51_3 i).1 (forms51_3 i).2 c.val e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 i).1 (forms51_3 i).2 c.val d.val e.val = true →
      test51 11 (forms51_3 i).1 (forms51_3 i).2 c.val d.val e.val = true →
      test51 13 (forms51_3 i).1 (forms51_3 i).2 c.val d.val e.val = true →
      False := by
  fin_cases i
  · simpa using exclude51_forms_block0
  · simpa using exclude51_forms_block1
  · simpa using exclude51_forms_block2

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
abbrev test55 (q b c a d e : Nat) : Bool :=
  positionTest 55 q [(3, 0), (11, b), (11, c), (683, a), (2971, d), (48912491, e)]
private theorem classify55_5 :
    ∀ a : Fin 55, test55_5 a.val = true → a.val = 1 ∨ a.val = 54 := by
  decide +kernel
private theorem classify55_11 :
    ∀ b c : Fin 55, test55_11 b.val c.val = true →
      ∃ i : Fin 19, b.val = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2 := by
  decide +kernel
private theorem exclude55_a1_block0 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block1 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block2 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block3 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block4 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block5 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block6 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block7 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block8 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block9 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block10 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block11 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block12 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block13 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block14 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block15 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block16 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block17 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block18 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1 (i : Fin 19) :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 i).1 (forms55_11 i).2 1 d.val e.val = true →
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

private theorem exclude55_a54_block0 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block1 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block2 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block3 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block4 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block5 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block6 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block7 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block8 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block9 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block10 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block11 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block12 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block13 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block14 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block15 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block16 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block17 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block18 :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54 (i : Fin 19) :
    ∀ d e : Fin 55,
      test55 3 (forms55_11 i).1 (forms55_11 i).2 54 d.val e.val = true →
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

theorem exclude55 (b c a d e : Fin 55)
    (h5 : test55_5 a.val = true)
    (h11 : test55_11 b.val c.val = true)
    (h3 : test55 3 b.val c.val a.val d.val e.val = true)
    (h13 : test55 13 b.val c.val a.val d.val e.val = true)
    (h17 : test55 17 b.val c.val a.val d.val e.val = true) : False := by
  obtain ⟨i, hb, hc⟩ := classify55_11 b c h11
  rcases classify55_5 a h5 with ha | ha
  · exact exclude55_a1 i d e
      (by simpa only [hb, hc, ha] using h3)
      (by simpa only [hb, hc, ha] using h13)
      (by simpa only [hb, hc, ha] using h17)
  · exact exclude55_a54 i d e
      (by simpa only [hb, hc, ha] using h3)
      (by simpa only [hb, hc, ha] using h13)
      (by simpa only [hb, hc, ha] using h17)

end A245211New
