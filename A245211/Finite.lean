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
private theorem exclude45_forms_block0_slice0 :
    ∀ e : Fin 45, 0 ≤ e.val → e.val < 9 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block0_slice1 :
    ∀ e : Fin 45, 9 ≤ e.val → e.val < 18 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block0_slice2 :
    ∀ e : Fin 45, 18 ≤ e.val → e.val < 27 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block0_slice3 :
    ∀ e : Fin 45, 27 ≤ e.val → e.val < 36 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block0_slice4 :
    ∀ e : Fin 45, 36 ≤ e.val → e.val < 45 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block0 (e : Fin 45) :
    ∀ f : Fin 45,
      test45 7 (forms45_5 (0 : Fin 13)).1 (forms45_5 (0 : Fin 13)).2.1 (forms45_5 (0 : Fin 13)).2.2.1 (forms45_5 (0 : Fin 13)).2.2.2 e.val f.val = true →
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
private theorem exclude45_forms_block1 :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
      test45 7 (forms45_5 (1 : Fin 13)).1 (forms45_5 (1 : Fin 13)).2.1 (forms45_5 (1 : Fin 13)).2.2.1 (forms45_5 (1 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (1 : Fin 13)).1 (forms45_5 (1 : Fin 13)).2.1 (forms45_5 (1 : Fin 13)).2.2.1 (forms45_5 (1 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (1 : Fin 13)).1 (forms45_5 (1 : Fin 13)).2.1 (forms45_5 (1 : Fin 13)).2.2.1 (forms45_5 (1 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e f h7 h13 h19
  have htest (q : Nat) : test45 q 42 44 43 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)]
      (by decide : List.Perm [(3, 42), (3, 44), (3, 43)] [(3, 42), (3, 43), (3, 44)]))
  exact exclude45_forms_block0 e f
    ((htest 7).symm.trans h7) ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
private theorem exclude45_forms_block2 :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
      test45 7 (forms45_5 (2 : Fin 13)).1 (forms45_5 (2 : Fin 13)).2.1 (forms45_5 (2 : Fin 13)).2.2.1 (forms45_5 (2 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (2 : Fin 13)).1 (forms45_5 (2 : Fin 13)).2.1 (forms45_5 (2 : Fin 13)).2.2.1 (forms45_5 (2 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (2 : Fin 13)).1 (forms45_5 (2 : Fin 13)).2.1 (forms45_5 (2 : Fin 13)).2.2.1 (forms45_5 (2 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e f h7 h13 h19
  have htest (q : Nat) : test45 q 43 42 44 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)]
      (by decide : List.Perm [(3, 43), (3, 42), (3, 44)] [(3, 42), (3, 43), (3, 44)]))
  exact exclude45_forms_block0 e f
    ((htest 7).symm.trans h7) ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
private theorem exclude45_forms_block3 :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
      test45 7 (forms45_5 (3 : Fin 13)).1 (forms45_5 (3 : Fin 13)).2.1 (forms45_5 (3 : Fin 13)).2.2.1 (forms45_5 (3 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (3 : Fin 13)).1 (forms45_5 (3 : Fin 13)).2.1 (forms45_5 (3 : Fin 13)).2.2.1 (forms45_5 (3 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (3 : Fin 13)).1 (forms45_5 (3 : Fin 13)).2.1 (forms45_5 (3 : Fin 13)).2.2.1 (forms45_5 (3 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e f h7 h13 h19
  have htest (q : Nat) : test45 q 43 44 42 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)]
      (by decide : List.Perm [(3, 43), (3, 44), (3, 42)] [(3, 42), (3, 43), (3, 44)]))
  exact exclude45_forms_block0 e f
    ((htest 7).symm.trans h7) ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
private theorem exclude45_forms_block4_slice0 :
    ∀ e : Fin 45, 0 ≤ e.val → e.val < 9 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block4_slice1 :
    ∀ e : Fin 45, 9 ≤ e.val → e.val < 18 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block4_slice2 :
    ∀ e : Fin 45, 18 ≤ e.val → e.val < 27 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block4_slice3 :
    ∀ e : Fin 45, 27 ≤ e.val → e.val < 36 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block4_slice4 :
    ∀ e : Fin 45, 36 ≤ e.val → e.val < 45 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block4 (e : Fin 45) :
    ∀ f : Fin 45,
      test45 7 (forms45_5 (4 : Fin 13)).1 (forms45_5 (4 : Fin 13)).2.1 (forms45_5 (4 : Fin 13)).2.2.1 (forms45_5 (4 : Fin 13)).2.2.2 e.val f.val = true →
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
private theorem exclude45_forms_block5_slice0 :
    ∀ e : Fin 45, 0 ≤ e.val → e.val < 9 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block5_slice1 :
    ∀ e : Fin 45, 9 ≤ e.val → e.val < 18 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block5_slice2 :
    ∀ e : Fin 45, 18 ≤ e.val → e.val < 27 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block5_slice3 :
    ∀ e : Fin 45, 27 ≤ e.val → e.val < 36 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block5_slice4 :
    ∀ e : Fin 45, 36 ≤ e.val → e.val < 45 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block5 (e : Fin 45) :
    ∀ f : Fin 45,
      test45 7 (forms45_5 (5 : Fin 13)).1 (forms45_5 (5 : Fin 13)).2.1 (forms45_5 (5 : Fin 13)).2.2.1 (forms45_5 (5 : Fin 13)).2.2.2 e.val f.val = true →
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
private theorem exclude45_forms_block6 :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
      test45 7 (forms45_5 (6 : Fin 13)).1 (forms45_5 (6 : Fin 13)).2.1 (forms45_5 (6 : Fin 13)).2.2.1 (forms45_5 (6 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (6 : Fin 13)).1 (forms45_5 (6 : Fin 13)).2.1 (forms45_5 (6 : Fin 13)).2.2.1 (forms45_5 (6 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (6 : Fin 13)).1 (forms45_5 (6 : Fin 13)).2.1 (forms45_5 (6 : Fin 13)).2.2.1 (forms45_5 (6 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e f h7 h13 h19
  have htest (q : Nat) : test45 q 44 42 43 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)]
      (by decide : List.Perm [(3, 44), (3, 42), (3, 43)] [(3, 42), (3, 43), (3, 44)]))
  exact exclude45_forms_block0 e f
    ((htest 7).symm.trans h7) ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
private theorem exclude45_forms_block7 :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
      test45 7 (forms45_5 (7 : Fin 13)).1 (forms45_5 (7 : Fin 13)).2.1 (forms45_5 (7 : Fin 13)).2.2.1 (forms45_5 (7 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (7 : Fin 13)).1 (forms45_5 (7 : Fin 13)).2.1 (forms45_5 (7 : Fin 13)).2.2.1 (forms45_5 (7 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (7 : Fin 13)).1 (forms45_5 (7 : Fin 13)).2.1 (forms45_5 (7 : Fin 13)).2.2.1 (forms45_5 (7 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e f h7 h13 h19
  have htest (q : Nat) : test45 q 44 43 42 1 e.val f.val =
      test45 q 42 43 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)]
      (by decide : List.Perm [(3, 44), (3, 43), (3, 42)] [(3, 42), (3, 43), (3, 44)]))
  exact exclude45_forms_block0 e f
    ((htest 7).symm.trans h7) ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
private theorem exclude45_forms_block8 :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
      test45 7 (forms45_5 (8 : Fin 13)).1 (forms45_5 (8 : Fin 13)).2.1 (forms45_5 (8 : Fin 13)).2.2.1 (forms45_5 (8 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (8 : Fin 13)).1 (forms45_5 (8 : Fin 13)).2.1 (forms45_5 (8 : Fin 13)).2.2.1 (forms45_5 (8 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (8 : Fin 13)).1 (forms45_5 (8 : Fin 13)).2.1 (forms45_5 (8 : Fin 13)).2.2.1 (forms45_5 (8 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e f h7 h13 h19
  have htest (q : Nat) : test45 q 44 43 44 1 e.val f.val =
      test45 q 43 44 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)]
      (by decide : List.Perm [(3, 44), (3, 43), (3, 44)] [(3, 43), (3, 44), (3, 44)]))
  exact exclude45_forms_block4 e f
    ((htest 7).symm.trans h7) ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
private theorem exclude45_forms_block9 :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
      test45 7 (forms45_5 (9 : Fin 13)).1 (forms45_5 (9 : Fin 13)).2.1 (forms45_5 (9 : Fin 13)).2.2.1 (forms45_5 (9 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (9 : Fin 13)).1 (forms45_5 (9 : Fin 13)).2.1 (forms45_5 (9 : Fin 13)).2.2.1 (forms45_5 (9 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (9 : Fin 13)).1 (forms45_5 (9 : Fin 13)).2.1 (forms45_5 (9 : Fin 13)).2.2.1 (forms45_5 (9 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e f h7 h13 h19
  have htest (q : Nat) : test45 q 44 43 44 43 e.val f.val =
      test45 q 43 44 44 43 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 43), (331, e.val), (18837001, f.val)]
      (by decide : List.Perm [(3, 44), (3, 43), (3, 44)] [(3, 43), (3, 44), (3, 44)]))
  exact exclude45_forms_block5 e f
    ((htest 7).symm.trans h7) ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
private theorem exclude45_forms_block10 :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
      test45 7 (forms45_5 (10 : Fin 13)).1 (forms45_5 (10 : Fin 13)).2.1 (forms45_5 (10 : Fin 13)).2.2.1 (forms45_5 (10 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (10 : Fin 13)).1 (forms45_5 (10 : Fin 13)).2.1 (forms45_5 (10 : Fin 13)).2.2.1 (forms45_5 (10 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (10 : Fin 13)).1 (forms45_5 (10 : Fin 13)).2.1 (forms45_5 (10 : Fin 13)).2.2.1 (forms45_5 (10 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e f h7 h13 h19
  have htest (q : Nat) : test45 q 44 44 43 1 e.val f.val =
      test45 q 43 44 44 1 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 1), (331, e.val), (18837001, f.val)]
      (by decide : List.Perm [(3, 44), (3, 44), (3, 43)] [(3, 43), (3, 44), (3, 44)]))
  exact exclude45_forms_block4 e f
    ((htest 7).symm.trans h7) ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
private theorem exclude45_forms_block11 :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
      test45 7 (forms45_5 (11 : Fin 13)).1 (forms45_5 (11 : Fin 13)).2.1 (forms45_5 (11 : Fin 13)).2.2.1 (forms45_5 (11 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (11 : Fin 13)).1 (forms45_5 (11 : Fin 13)).2.1 (forms45_5 (11 : Fin 13)).2.2.1 (forms45_5 (11 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (11 : Fin 13)).1 (forms45_5 (11 : Fin 13)).2.1 (forms45_5 (11 : Fin 13)).2.2.1 (forms45_5 (11 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  intro e f h7 h13 h19
  have htest (q : Nat) : test45 q 44 44 43 43 e.val f.val =
      test45 q 43 44 44 43 e.val f.val := by
    exact positionTest_perm 45 q (List.Perm.append_right [(11, 0), (19, 43), (331, e.val), (18837001, f.val)]
      (by decide : List.Perm [(3, 44), (3, 44), (3, 43)] [(3, 43), (3, 44), (3, 44)]))
  exact exclude45_forms_block5 e f
    ((htest 7).symm.trans h7) ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)
private theorem exclude45_forms_block12_slice0 :
    ∀ e : Fin 45, 0 ≤ e.val → e.val < 9 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block12_slice1 :
    ∀ e : Fin 45, 9 ≤ e.val → e.val < 18 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block12_slice2 :
    ∀ e : Fin 45, 18 ≤ e.val → e.val < 27 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block12_slice3 :
    ∀ e : Fin 45, 27 ≤ e.val → e.val < 36 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block12_slice4 :
    ∀ e : Fin 45, 36 ≤ e.val → e.val < 45 →
      ∀ f : Fin 45,
      test45 7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 13 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      test45 19 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
      False := by
  decide +kernel
private theorem exclude45_forms_block12 (e : Fin 45) :
    ∀ f : Fin 45,
      test45 7 (forms45_5 (12 : Fin 13)).1 (forms45_5 (12 : Fin 13)).2.1 (forms45_5 (12 : Fin 13)).2.2.1 (forms45_5 (12 : Fin 13)).2.2.2 e.val f.val = true →
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
private theorem exclude45_forms (j : Fin 13) :
    ∀ e : Fin 45,
      ∀ f : Fin 45,
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
private theorem exclude51_forms_block0_slot0_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 20 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot0_slice1 :
    ∀ e : Fin 51, 20 ≤ e.val → e.val < 44 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot0_slice2 :
    ∀ e : Fin 51, 44 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 0 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot1_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 25 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot1_slice1 :
    ∀ e : Fin 51, 25 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 1 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot2 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 2 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 2 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 2 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 2 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot3 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 3 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 3 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 3 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 3 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot4 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 4 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 4 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 4 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 4 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot5 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 5 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 5 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 5 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 5 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot6 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 6 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 6 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 6 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 6 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot7 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 7 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 7 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 7 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 7 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot8 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 8 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 8 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 8 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 8 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot9 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 9 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 9 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 9 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 9 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot10 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 10 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 10 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 10 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 10 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot11 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 11 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 11 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 11 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 11 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot12 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 12 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 12 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 12 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 12 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot13 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 13 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 13 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 13 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 13 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot14 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 14 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 14 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 14 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 14 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot15 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 15 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 15 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 15 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 15 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot16 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 16 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 16 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 16 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 16 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot17 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 17 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 17 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 17 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 17 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot18 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 18 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 18 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 18 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 18 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot19 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 19 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 19 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 19 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 19 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot20 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 20 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 20 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 20 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 20 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot21 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 21 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 21 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 21 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 21 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot22 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 22 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 22 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 22 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 22 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot23 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 23 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 23 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 23 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 23 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot24_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot24_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 24 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot25 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 25 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 25 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 25 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 25 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot26 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 26 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 26 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 26 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 26 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot27_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot27_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 27 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot28_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot28_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 28 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot29 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 29 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 29 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 29 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 29 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot30_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot30_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 30 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot31_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot31_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 31 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot32 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 32 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 32 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 32 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 32 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot33_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot33_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 33 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot34_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot34_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 34 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot35 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 35 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 35 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 35 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 35 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot36_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot36_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 36 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot37_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot37_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 37 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot38 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 38 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 38 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 38 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 38 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot39_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot39_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 39 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot40_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot40_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 40 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot41 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 41 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 41 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 41 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 41 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot42_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot42_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 42 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot43_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot43_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 43 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot44 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 44 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 44 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 44 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 44 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot45_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot45_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 45 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot46_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot46_slice1 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 46 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot47 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 47 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 47 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 47 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 47 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot48_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot48_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 46 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot48_slice2 :
    ∀ e : Fin 51, 46 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 48 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot49_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 12 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot49_slice1 :
    ∀ e : Fin 51, 12 ≤ e.val → e.val < 24 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot49_slice2 :
    ∀ e : Fin 51, 24 ≤ e.val → e.val < 36 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot49_slice3 :
    ∀ e : Fin 51, 36 ≤ e.val → e.val < 48 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block0_slot49_slice4 :
    ∀ e : Fin 51, 48 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block0_slot50 :
    ∀ e : Fin 51, test51_7 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (0 : Fin 3)).1 (forms51_3 (0 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot0 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 0 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 0 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 0 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 0 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot1 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 1 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 1 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 1 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot2 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 2 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 2 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 2 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 2 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot3 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 3 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 3 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 3 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 3 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot4 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 4 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 4 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 4 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 4 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot5 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 5 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 5 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 5 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 5 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot6 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 6 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 6 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 6 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 6 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot7 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 7 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 7 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 7 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 7 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot8 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 8 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 8 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 8 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 8 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot9 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 9 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 9 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 9 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 9 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot10 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 10 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 10 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 10 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 10 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot11 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 11 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 11 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 11 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 11 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot12 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 12 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 12 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 12 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 12 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot13 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 13 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 13 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 13 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 13 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot14 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 14 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 14 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 14 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 14 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot15 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 15 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 15 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 15 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 15 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot16 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 16 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 16 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 16 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 16 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot17 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 17 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 17 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 17 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 17 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot18 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 18 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 18 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 18 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 18 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot19 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 19 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 19 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 19 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 19 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot20 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 20 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 20 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 20 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 20 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot21 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 21 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 21 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 21 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 21 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot22 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 22 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 22 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 22 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 22 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot23 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 23 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 23 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 23 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 23 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot24 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 24 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 24 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 24 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 24 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot25_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot25_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 25 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot26_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot26_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 26 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot27 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 27 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 27 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 27 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 27 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot28_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot28_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 28 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot29_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot29_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 29 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot30 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 30 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 30 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 30 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 30 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot31_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot31_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 31 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot32_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot32_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 32 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot33 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 33 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 33 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 33 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 33 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot34_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot34_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 34 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot35_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot35_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 35 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot36 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 36 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 36 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 36 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 36 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot37_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot37_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 37 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot38_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot38_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 38 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot39 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 39 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 39 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 39 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 39 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot40_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot40_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 40 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot41_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot41_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 41 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot42 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 42 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 42 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 42 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 42 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot43_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot43_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 43 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot44_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot44_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 44 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot45 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 45 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 45 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 45 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 45 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot46_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot46_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 46 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot47_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 22 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot47_slice1 :
    ∀ e : Fin 51, 22 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 47 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot48 :
    ∀ e : Fin 51, test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 48 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 48 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 48 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 48 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot49_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot49_slice1 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 47 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot49_slice2 :
    ∀ e : Fin 51, 47 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 49 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude51_forms_block2_slot50_slice0 :
    ∀ e : Fin 51, 0 ≤ e.val → e.val < 11 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot50_slice1 :
    ∀ e : Fin 51, 11 ≤ e.val → e.val < 23 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot50_slice2 :
    ∀ e : Fin 51, 23 ≤ e.val → e.val < 35 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot50_slice3 :
    ∀ e : Fin 51, 35 ≤ e.val → e.val < 47 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude51_forms_block2_slot50_slice4 :
    ∀ e : Fin 51, 47 ≤ e.val → e.val < 51 →
      test51_7 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 e.val = true →
      ∀ d : Fin 51,
      test51 5 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 11 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      test51 13 (forms51_3 (2 : Fin 3)).1 (forms51_3 (2 : Fin 3)).2 50 d.val e.val = true →
      False := by
  decide +kernel
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
private theorem exclude55_a1_block0_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block0_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block0_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block0_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block0_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block0 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block0_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block0_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block0_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block0_slice3 d (by omega) h3
  exact exclude55_a1_block0_slice4 d (by omega) (by omega)
private theorem exclude55_a1_block1_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block1_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block1_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block1_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block1_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block1 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block1_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block1_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block1_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block1_slice3 d (by omega) h3
  exact exclude55_a1_block1_slice4 d (by omega) (by omega)
private theorem exclude55_a1_block2_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block2_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block2_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block2_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block2_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block2 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block2_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block2_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block2_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block2_slice3 d (by omega) h3
  exact exclude55_a1_block2_slice4 d (by omega) (by omega)
private theorem exclude55_a1_block3_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block3_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block3_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block3_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block3_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block3 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block3_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block3_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block3_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block3_slice3 d (by omega) h3
  exact exclude55_a1_block3_slice4 d (by omega) (by omega)
private theorem exclude55_a1_block4_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block4_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block4_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block4_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block4_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block4 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block4_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block4_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block4_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block4_slice3 d (by omega) h3
  exact exclude55_a1_block4_slice4 d (by omega) (by omega)
private theorem exclude55_a1_block5_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block5_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block5_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block5_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block5_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block5 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block5_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block5_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block5_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block5_slice3 d (by omega) h3
  exact exclude55_a1_block5_slice4 d (by omega) (by omega)
private theorem exclude55_a1_block6_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block6_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block6_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block6_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block6_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block6 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block6_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block6_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block6_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block6_slice3 d (by omega) h3
  exact exclude55_a1_block6_slice4 d (by omega) (by omega)
private theorem exclude55_a1_block7_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block7_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block7_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block7_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block7_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block7 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block7_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block7_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block7_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block7_slice3 d (by omega) h3
  exact exclude55_a1_block7_slice4 d (by omega) (by omega)
private theorem exclude55_a1_block8_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block8_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block8_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block8_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block8_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block8 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block8_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block8_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block8_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block8_slice3 d (by omega) h3
  exact exclude55_a1_block8_slice4 d (by omega) (by omega)
private theorem exclude55_a1_block9 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 39 1 d.val e.val =
      test55 q 39 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 39)] [(11, 39), (11, 48)])))
  exact exclude55_a1_block0 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a1_block10 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 40 1 d.val e.val =
      test55 q 40 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 40)] [(11, 40), (11, 48)])))
  exact exclude55_a1_block1 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a1_block11 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 41 1 d.val e.val =
      test55 q 41 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 41)] [(11, 41), (11, 48)])))
  exact exclude55_a1_block2 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a1_block12 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 42 1 d.val e.val =
      test55 q 42 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 42)] [(11, 42), (11, 48)])))
  exact exclude55_a1_block3 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a1_block13 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 43 1 d.val e.val =
      test55 q 43 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 43)] [(11, 43), (11, 48)])))
  exact exclude55_a1_block4 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a1_block14 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 44 1 d.val e.val =
      test55 q 44 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 44)] [(11, 44), (11, 48)])))
  exact exclude55_a1_block5 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a1_block15 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 45 1 d.val e.val =
      test55 q 45 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 45)] [(11, 45), (11, 48)])))
  exact exclude55_a1_block6 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a1_block16 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 46 1 d.val e.val =
      test55 q 46 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 46)] [(11, 46), (11, 48)])))
  exact exclude55_a1_block7 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a1_block17 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 1 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 47 1 d.val e.val =
      test55 q 47 48 1 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 1), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 47)] [(11, 47), (11, 48)])))
  exact exclude55_a1_block8 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a1_block18_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block18_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block18_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block18_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block18_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a1_block18 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 1 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a1_block18_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a1_block18_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a1_block18_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a1_block18_slice3 d (by omega) h3
  exact exclude55_a1_block18_slice4 d (by omega) (by omega)
private theorem exclude55_a1 (i : Fin 19) :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
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

private theorem exclude55_a54_block0_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block0_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block0_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block0_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block0_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block0 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (0 : Fin 19)).1 (forms55_11 (0 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block0_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block0_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block0_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block0_slice3 d (by omega) h3
  exact exclude55_a54_block0_slice4 d (by omega) (by omega)
private theorem exclude55_a54_block1_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block1_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block1_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block1_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block1_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block1 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (1 : Fin 19)).1 (forms55_11 (1 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block1_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block1_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block1_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block1_slice3 d (by omega) h3
  exact exclude55_a54_block1_slice4 d (by omega) (by omega)
private theorem exclude55_a54_block2_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block2_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block2_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block2_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block2_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block2 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (2 : Fin 19)).1 (forms55_11 (2 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block2_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block2_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block2_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block2_slice3 d (by omega) h3
  exact exclude55_a54_block2_slice4 d (by omega) (by omega)
private theorem exclude55_a54_block3_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block3_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block3_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block3_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block3_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block3 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (3 : Fin 19)).1 (forms55_11 (3 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block3_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block3_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block3_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block3_slice3 d (by omega) h3
  exact exclude55_a54_block3_slice4 d (by omega) (by omega)
private theorem exclude55_a54_block4_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block4_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block4_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block4_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block4_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block4 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (4 : Fin 19)).1 (forms55_11 (4 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block4_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block4_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block4_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block4_slice3 d (by omega) h3
  exact exclude55_a54_block4_slice4 d (by omega) (by omega)
private theorem exclude55_a54_block5_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block5_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block5_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block5_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block5_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block5 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (5 : Fin 19)).1 (forms55_11 (5 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block5_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block5_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block5_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block5_slice3 d (by omega) h3
  exact exclude55_a54_block5_slice4 d (by omega) (by omega)
private theorem exclude55_a54_block6_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block6_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block6_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block6_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block6_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block6 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (6 : Fin 19)).1 (forms55_11 (6 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block6_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block6_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block6_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block6_slice3 d (by omega) h3
  exact exclude55_a54_block6_slice4 d (by omega) (by omega)
private theorem exclude55_a54_block7_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block7_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block7_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block7_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block7_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block7 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (7 : Fin 19)).1 (forms55_11 (7 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block7_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block7_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block7_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block7_slice3 d (by omega) h3
  exact exclude55_a54_block7_slice4 d (by omega) (by omega)
private theorem exclude55_a54_block8_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block8_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block8_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block8_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block8_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block8 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (8 : Fin 19)).1 (forms55_11 (8 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block8_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block8_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block8_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block8_slice3 d (by omega) h3
  exact exclude55_a54_block8_slice4 d (by omega) (by omega)
private theorem exclude55_a54_block9 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (9 : Fin 19)).1 (forms55_11 (9 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 39 54 d.val e.val =
      test55 q 39 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 39)] [(11, 39), (11, 48)])))
  exact exclude55_a54_block0 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a54_block10 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (10 : Fin 19)).1 (forms55_11 (10 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 40 54 d.val e.val =
      test55 q 40 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 40)] [(11, 40), (11, 48)])))
  exact exclude55_a54_block1 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a54_block11 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (11 : Fin 19)).1 (forms55_11 (11 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 41 54 d.val e.val =
      test55 q 41 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 41)] [(11, 41), (11, 48)])))
  exact exclude55_a54_block2 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a54_block12 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (12 : Fin 19)).1 (forms55_11 (12 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 42 54 d.val e.val =
      test55 q 42 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 42)] [(11, 42), (11, 48)])))
  exact exclude55_a54_block3 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a54_block13 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (13 : Fin 19)).1 (forms55_11 (13 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 43 54 d.val e.val =
      test55 q 43 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 43)] [(11, 43), (11, 48)])))
  exact exclude55_a54_block4 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a54_block14 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (14 : Fin 19)).1 (forms55_11 (14 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 44 54 d.val e.val =
      test55 q 44 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 44)] [(11, 44), (11, 48)])))
  exact exclude55_a54_block5 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a54_block15 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (15 : Fin 19)).1 (forms55_11 (15 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 45 54 d.val e.val =
      test55 q 45 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 45)] [(11, 45), (11, 48)])))
  exact exclude55_a54_block6 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a54_block16 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (16 : Fin 19)).1 (forms55_11 (16 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 46 54 d.val e.val =
      test55 q 46 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 46)] [(11, 46), (11, 48)])))
  exact exclude55_a54_block7 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a54_block17 :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
      test55 3 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (17 : Fin 19)).1 (forms55_11 (17 : Fin 19)).2 54 d.val e.val = true →
      False := by
  intro d e h3 h13 h17
  have htest (q : Nat) : test55 q 48 47 54 d.val e.val =
      test55 q 47 48 54 d.val e.val := by
    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right [(683, 54), (2971, d.val), (48912491, e.val)]
      (by decide : List.Perm [(11, 48), (11, 47)] [(11, 47), (11, 48)])))
  exact exclude55_a54_block8 d e
    ((htest 3).symm.trans h3) ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)
private theorem exclude55_a54_block18_slice0 :
    ∀ d : Fin 55, 0 ≤ d.val → d.val < 11 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block18_slice1 :
    ∀ d : Fin 55, 11 ≤ d.val → d.val < 22 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block18_slice2 :
    ∀ d : Fin 55, 22 ≤ d.val → d.val < 33 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block18_slice3 :
    ∀ d : Fin 55, 33 ≤ d.val → d.val < 44 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block18_slice4 :
    ∀ d : Fin 55, 44 ≤ d.val → d.val < 55 →
      ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      False := by
  decide +kernel
private theorem exclude55_a54_block18 (d : Fin 55) :
    ∀ e : Fin 55,
      test55 3 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 13 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      test55 17 (forms55_11 (18 : Fin 19)).1 (forms55_11 (18 : Fin 19)).2 54 d.val e.val = true →
      False := by
  have hbound := d.isLt
  by_cases h0 : d.val < 11
  · exact exclude55_a54_block18_slice0 d (by omega) h0
  by_cases h1 : d.val < 22
  · exact exclude55_a54_block18_slice1 d (by omega) h1
  by_cases h2 : d.val < 33
  · exact exclude55_a54_block18_slice2 d (by omega) h2
  by_cases h3 : d.val < 44
  · exact exclude55_a54_block18_slice3 d (by omega) h3
  exact exclude55_a54_block18_slice4 d (by omega) (by omega)
private theorem exclude55_a54 (i : Fin 19) :
    ∀ d : Fin 55,
      ∀ e : Fin 55,
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
