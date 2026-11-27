import Mathlib

/-!
# A finite certificate for six-vertex triangle-free graphs

We encode a labelled graph by the fifteen bits of its upper triangular adjacency
matrix, in lexicographic edge order.  The certificate searches only vertex cuts:
the last vertex has colour `false`, so there are thirty-two cuts to consider.

Each closed finite assertion below is checked by reduction in Lean's kernel.
No result of an external program is used as a proof.
-/

namespace SixVertex

/-- The fifteen possible edges, in lexicographic order. -/
def edges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
   (1, 2), (1, 3), (1, 4), (1, 5),
   (2, 3), (2, 4), (2, 5),
   (3, 4), (3, 5), (4, 5)]

/-- The edge indices of the twenty possible triangles. -/
def triangleEdges : List (Nat × Nat × Nat) :=
  [(0, 1, 5), (0, 2, 6), (0, 3, 7), (0, 4, 8),
   (1, 2, 9), (1, 3, 10), (1, 4, 11),
   (2, 3, 12), (2, 4, 13), (3, 4, 14),
   (5, 6, 9), (5, 7, 10), (5, 8, 11),
   (6, 7, 12), (6, 8, 13), (7, 8, 14),
   (9, 10, 12), (9, 11, 13), (10, 11, 14), (12, 13, 14)]

/-- The graph mask contains none of the twenty triangles. -/
def TriFree (m : Nat) : Prop :=
  triangleEdges.all (fun t =>
    !(m.testBit t.1 && m.testBit t.2.1 && m.testBit t.2.2)) = true

instance decidableTriFree (m : Nat) : Decidable (TriFree m) :=
  inferInstanceAs (Decidable
    (triangleEdges.all (fun t =>
      !(m.testBit t.1 && m.testBit t.2.1 && m.testBit t.2.2)) = true))

/-- A propositional form of the Boolean triangle check, for the graph bridge. -/
theorem triFree_iff (m : Nat) :
    TriFree m ↔ ∀ t ∈ triangleEdges,
      ¬ (m.testBit t.1 = true ∧ m.testBit t.2.1 = true ∧
        m.testBit t.2.2 = true) := by
  unfold TriFree
  rw [List.all_eq_true]
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _
  cases m.testBit t.1 <;> cases m.testBit t.2.1 <;>
    cases m.testBit t.2.2 <;> decide

/-- Present edges whose endpoints have the same vertex colour. -/
def monoEdges (m col : Nat) : Finset Nat :=
  (Finset.range 15).filter (fun i =>
    m.testBit i = true ∧
      col.testBit (edges[i]!.1) = col.testBit (edges[i]!.2))

/-- The cut leaves at most one monochromatic edge. -/
def Good (m col : Nat) : Prop := (monoEdges m col).card ≤ 1

instance decidableGood (m col : Nat) : Decidable (Good m col) :=
  inferInstanceAs (Decidable ((monoEdges m col).card ≤ 1))

/-- Any two monochromatic edges of a good cut have the same index. -/
theorem good_unique {m col : Nat} (h : Good m col) {i j : Nat}
    (hi : i < 15) (hj : j < 15)
    (hmi : m.testBit i = true) (hmj : m.testBit j = true)
    (hci : col.testBit (edges[i]!.1) = col.testBit (edges[i]!.2))
    (hcj : col.testBit (edges[j]!.1) = col.testBit (edges[j]!.2)) :
    i = j := by
  have hcard : (monoEdges m col).card ≤ 1 := h
  apply (Finset.card_le_one.mp hcard) i _ j _
  · simp [monoEdges, hi, hmi, hci]
  · simp [monoEdges, hj, hmj, hcj]

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem block0 :
    ∀ r : Fin 4096, TriFree r.val →
      ∃ col : Fin 32, Good r.val col.val := by
  decide +kernel

private theorem block1 :
    ∀ r : Fin 4096, TriFree (4096 + r.val) →
      ∃ col : Fin 32, Good (4096 + r.val) col.val := by
  decide +kernel

private theorem block2 :
    ∀ r : Fin 4096, TriFree (8192 + r.val) →
      ∃ col : Fin 32, Good (8192 + r.val) col.val := by
  decide +kernel

private theorem block3 :
    ∀ r : Fin 4096, TriFree (12288 + r.val) →
      ∃ col : Fin 32, Good (12288 + r.val) col.val := by
  decide +kernel

private theorem block4 :
    ∀ r : Fin 4096, TriFree (16384 + r.val) →
      ∃ col : Fin 32, Good (16384 + r.val) col.val := by
  decide +kernel

private theorem block5 :
    ∀ r : Fin 4096, TriFree (20480 + r.val) →
      ∃ col : Fin 32, Good (20480 + r.val) col.val := by
  decide +kernel

private theorem block6 :
    ∀ r : Fin 4096, TriFree (24576 + r.val) →
      ∃ col : Fin 32, Good (24576 + r.val) col.val := by
  decide +kernel

private theorem block7 :
    ∀ r : Fin 4096, TriFree (28672 + r.val) →
      ∃ col : Fin 32, Good (28672 + r.val) col.val := by
  decide +kernel

private theorem allBlocks (q : Fin 8) :
    ∀ r : Fin 4096, TriFree (q.val * 4096 + r.val) →
      ∃ col : Fin 32, Good (q.val * 4096 + r.val) col.val := by
  fin_cases q
  · simpa using block0
  · simpa using block1
  · simpa using block2
  · simpa using block3
  · simpa using block4
  · simpa using block5
  · simpa using block6
  · simpa using block7

/-- Every triangle-free six-vertex graph has a cut with at most one bad edge. -/
theorem mask_good (m : Nat) (hm : m < 32768) (ht : TriFree m) :
    ∃ col : Nat, col < 64 ∧ Good m col := by
  let q : Fin 8 := ⟨m / 4096, by omega⟩
  let r : Fin 4096 := ⟨m % 4096, Nat.mod_lt _ (by decide)⟩
  have hdecomp : q.val * 4096 + r.val = m := by
    dsimp [q, r]
    omega
  obtain ⟨col, hcol⟩ := allBlocks q r (by simpa [hdecomp] using ht)
  refine ⟨col.val, ?_, ?_⟩
  · have := col.isLt
    omega
  · simpa [hdecomp] using hcol

end SixVertex
