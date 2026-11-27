import Mathlib
import Batteries.Data.Nat.Lemmas
import SixVertex.Finite

/-!
# From finite graph masks to edge-colour avoidance

The finite certificate only concerns ordinary vertex cuts.  This file connects
its fifteen-bit representation to arbitrary simple graphs on at most six
vertices, then applies a global interchange of the two vertex colours when
the unique possible monochromatic edge has the forbidden colour.
-/

namespace SixVertex

universe u

/-- Adjacency of the original vertices, viewed inside the natural numbers.
Numbers outside `Fin k` are isolated. -/
def paddedAdj {k : Nat} (G : SimpleGraph (Fin k)) (a b : Nat) : Prop :=
  ∃ x y : Fin k, x.val = a ∧ y.val = b ∧ G.Adj x y

/-- The fifteen upper-triangular adjacency bits of the padded graph. -/
noncomputable def encodeMask {k : Nat} (G : SimpleGraph (Fin k)) : Nat := by
  classical
  exact Nat.ofBits (fun i : Fin 15 =>
    decide (paddedAdj G (edges[i.val]!.1) (edges[i.val]!.2)))

theorem encodeMask_lt {k : Nat} (G : SimpleGraph (Fin k)) :
    encodeMask G < 32768 := by
  classical
  simpa [encodeMask] using
    (Nat.ofBits_lt_two_pow (fun i : Fin 15 =>
      decide (paddedAdj G (edges[i.val]!.1) (edges[i.val]!.2))))

theorem encodeMask_bit {k : Nat} (G : SimpleGraph (Fin k)) (i : Fin 15) :
    (encodeMask G).testBit i.val = true ↔
      paddedAdj G (edges[i.val]!.1) (edges[i.val]!.2) := by
  classical
  simp [encodeMask, Nat.testBit_ofBits_lt, i.isLt]

private theorem padded_triangle_false {k : Nat} {G : SimpleGraph (Fin k)}
    (ht : G.CliqueFree 3) {a b c : Nat}
    (hab : paddedAdj G a b) (hac : paddedAdj G a c)
    (hbc : paddedAdj G b c) : False := by
  rcases hab with ⟨x, y, hx, hy, hxy⟩
  rcases hac with ⟨x', z, hx', hz, hxz⟩
  rcases hbc with ⟨y', z', hy', hz', hyz⟩
  have hxx : x' = x := Fin.ext (hx'.trans hx.symm)
  have hyy : y' = y := Fin.ext (hy'.trans hy.symm)
  have hzz : z' = z := Fin.ext (hz'.trans hz.symm)
  subst x' y' z'
  exact ht {x, y, z} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)

/-- The Boolean triangle predicate follows from the standard graph predicate. -/
theorem encodeMask_triFree {k : Nat} (G : SimpleGraph (Fin k))
    (ht : G.CliqueFree 3) : TriFree (encodeMask G) := by
  classical
  rw [triFree_iff]
  intro t hmem htriangle
  have hbounds : t.1 < 15 ∧ t.2.1 < 15 ∧ t.2.2 < 15 := by
    have hall : triangleEdges.all (fun s =>
        decide (s.1 < 15 ∧ s.2.1 < 15 ∧ s.2.2 < 15)) = true := by
      decide
    exact of_decide_eq_true ((List.all_eq_true.mp hall) t hmem)
  have ha := (encodeMask_bit G ⟨t.1, hbounds.1⟩).mp htriangle.1
  have hb := (encodeMask_bit G ⟨t.2.1, hbounds.2.1⟩).mp htriangle.2.1
  have hc := (encodeMask_bit G ⟨t.2.2, hbounds.2.2⟩).mp htriangle.2.2
  simp only [triangleEdges, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [edges] at ha hb hc
    exact padded_triangle_false ht ha hb hc

/-- Every unordered pair of distinct vertices occurs in the edge list. -/
private theorem edge_lookup (x y : Fin 6) (hxy : x ≠ y) :
    ∃ i : Fin 15,
      edges[i.val]! = (x.val, y.val) ∨ edges[i.val]! = (y.val, x.val) := by
  revert x y
  decide +kernel

/-- There is at most one undirected monochromatic edge. -/
def AtMostOneMono {V : Type u} (G : SimpleGraph V) (d : V → Bool) : Prop :=
  ∀ x y u v, G.Adj x y → G.Adj u v → d x = d y → d u = d v →
    (x = u ∧ y = v) ∨ (x = v ∧ y = u)

/-- The finite cut certificate applies to every triangle-free graph of order
at most six, with no assumption about connectedness or isolated vertices. -/
theorem exists_atMostOneMono (k : Nat) (G : SimpleGraph (Fin k))
    (hk : k ≤ 6) (ht : G.CliqueFree 3) :
    ∃ d : Fin k → Bool, AtMostOneMono G d := by
  classical
  obtain ⟨col, _, hgood⟩ :=
    mask_good (encodeMask G) (encodeMask_lt G) (encodeMask_triFree G ht)
  refine ⟨fun x => col.testBit x.val, ?_⟩
  intro x y u v hxy huv hdxy hduv
  let x6 : Fin 6 := ⟨x.val, lt_of_lt_of_le x.isLt hk⟩
  let y6 : Fin 6 := ⟨y.val, lt_of_lt_of_le y.isLt hk⟩
  let u6 : Fin 6 := ⟨u.val, lt_of_lt_of_le u.isLt hk⟩
  let v6 : Fin 6 := ⟨v.val, lt_of_lt_of_le v.isLt hk⟩
  have hxy6 : x6 ≠ y6 := by
    intro h
    exact hxy.ne (Fin.ext (congrArg (fun z : Fin 6 => z.val) h))
  have huv6 : u6 ≠ v6 := by
    intro h
    exact huv.ne (Fin.ext (congrArg (fun z : Fin 6 => z.val) h))
  obtain ⟨i, hi⟩ := edge_lookup x6 y6 hxy6
  obtain ⟨j, hj⟩ := edge_lookup u6 v6 huv6
  have hmi : (encodeMask G).testBit i.val = true := by
    apply (encodeMask_bit G i).mpr
    rcases hi with hi | hi
    · rw [hi]
      exact ⟨x, y, rfl, rfl, hxy⟩
    · rw [hi]
      exact ⟨y, x, rfl, rfl, hxy.symm⟩
  have hmj : (encodeMask G).testBit j.val = true := by
    apply (encodeMask_bit G j).mpr
    rcases hj with hj | hj
    · rw [hj]
      exact ⟨u, v, rfl, rfl, huv⟩
    · rw [hj]
      exact ⟨v, u, rfl, rfl, huv.symm⟩
  have hci : col.testBit (edges[i.val]!.1) = col.testBit (edges[i.val]!.2) := by
    rcases hi with hi | hi
    · simpa only [hi] using hdxy
    · simpa only [hi] using hdxy.symm
  have hcj : col.testBit (edges[j.val]!.1) = col.testBit (edges[j.val]!.2) := by
    rcases hj with hj | hj
    · simpa only [hj] using hduv
    · simpa only [hj] using hduv.symm
  have hij : i.val = j.val :=
    good_unique hgood i.isLt j.isLt hmi hmj hci hcj
  have he : edges[i.val]! = edges[j.val]! := congrArg (fun n => edges[n]!) hij
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have h := hi.symm.trans (he.trans hj)
    exact Or.inl ⟨Fin.ext (congrArg Prod.fst h), Fin.ext (congrArg Prod.snd h)⟩
  · have h := hi.symm.trans (he.trans hj)
    exact Or.inr ⟨Fin.ext (congrArg Prod.fst h), Fin.ext (congrArg Prod.snd h)⟩
  · have h := hi.symm.trans (he.trans hj)
    exact Or.inr ⟨Fin.ext (congrArg Prod.snd h), Fin.ext (congrArg Prod.fst h)⟩
  · have h := hi.symm.trans (he.trans hj)
    exact Or.inl ⟨Fin.ext (congrArg Prod.snd h), Fin.ext (congrArg Prod.fst h)⟩

/-- A global colour interchange makes the possible unique monochromatic edge
avoid its prescribed colour. This argument does not depend on the graph size. -/
theorem avoidance_of_atMostOneMono {V : Type u} (G : SimpleGraph V)
    (d : V → Bool) (hunique : AtMostOneMono G d)
    (c : V → V → Bool) (hsym : ∀ x y, c x y = c y x) :
    ∃ d' : V → Bool,
      ∀ x y, G.Adj x y → ¬ (d' x = c x y ∧ d' y = c x y) := by
  classical
  by_cases hmono : ∃ a b, G.Adj a b ∧ d a = d b
  · obtain ⟨a, b, hab, hdab⟩ := hmono
    by_cases hbad : d a = c a b
    · refine ⟨fun x => Bool.not (d x), ?_⟩
      intro x y hxy hforbidden
      have hsame : d x = d y := by
        have hflip : Bool.not (d x) = Bool.not (d y) :=
          hforbidden.1.trans hforbidden.2.symm
        simpa using congrArg Bool.not hflip
      rcases hunique x y a b hxy hab hsame hdab with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
      · subst x y
        have hcontra : Bool.not (d a) = d a := hforbidden.1.trans hbad.symm
        cases hda : d a <;> simp [hda] at hcontra
      · subst x y
        have hcontra : Bool.not (d a) = d a :=
          hforbidden.2.trans ((hsym b a).trans hbad.symm)
        cases hda : d a <;> simp [hda] at hcontra
    · refine ⟨d, ?_⟩
      intro x y hxy hforbidden
      have hsame : d x = d y := hforbidden.1.trans hforbidden.2.symm
      rcases hunique x y a b hxy hab hsame hdab with ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
      · subst x y
        exact hbad hforbidden.1
      · subst x y
        exact hbad (hforbidden.2.trans (hsym b a))
  · refine ⟨d, ?_⟩
    intro x y hxy hforbidden
    exact hmono ⟨x, y, hxy, hforbidden.1.trans hforbidden.2.symm⟩

/-- Every symmetric Boolean edge colouring of a triangle-free graph on at most
six vertices admits vertex colours avoiding a monochromatic edge in its own
edge colour. -/
theorem edge_color_avoidance (k : Nat) (G : SimpleGraph (Fin k))
    (hk : k ≤ 6) (ht : G.CliqueFree 3)
    (c : Fin k → Fin k → Bool) (hsym : ∀ x y, c x y = c y x) :
    ∃ d : Fin k → Bool,
      ∀ x y, G.Adj x y → ¬ (d x = c x y ∧ d y = c x y) := by
  obtain ⟨d, hd⟩ := exists_atMostOneMono k G hk ht
  exact avoidance_of_atMostOneMono G d hd c hsym

end SixVertex
