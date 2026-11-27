"""Generate the ordinary Lean assembly for the exact R2.H2 target."""
from pathlib import Path
from search_moduli import FACTORS

ROOT = Path(__file__).parent
out = []
def emit(s=''):
    out.append(s.rstrip()+'\n')

emit('''import A245211.Projection
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
''')

normal = {r:0 for r in FACTORS}
normal.update({45:3,51:5})
for r,fs in FACTORS.items():
    n=len(fs)
    j=normal[r]
    factor_list='['+', '.join(map(str,fs))+']'
    pairs=', '.join(f'({f}, '+('0' if i==j else f'(pos {i}).val')+')' for i,f in enumerate(fs))
    emit(f'abbrev factors{r} : List Nat := {factor_list}\n')
    emit(f'''theorem no_fixed_count{r} {{n : Nat}} (hs : Squarefree n)
    (hr : n.primeFactors.card = {r}) (ha : OeisA245211.a n = n) : False := by
  have hprime : ∀ q ∈ factors{r}, Nat.Prime q := by
    norm_num [factors{r}]
  have hfactor : factors{r}.prod = 2 ^ {r} + 1 := by
    norm_num [factors{r}]
  obtain ⟨pos, p, hzero, hp, hrec⟩ :=
    squarefree_token_cycle hs ha hr (by decide) factors{r} hprime hfactor ({j} : Fin {n})
  have hlarge (i : Fin {r}) : 33 < p i := by
    exact lt_trans (by norm_num : 33 < 2 ^ ({r} - 1)) (hp i).2
  have hspec : tokenSpec factors{r} pos = [{pairs}] := by
    simp [tokenSpec, factors{r}, List.ofFn_succ, hzero]
  have hprojected (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest {r} q (projectedTokenSpec q factors{r} pos) = true :=
    positionTest_of_projected_token_cycle (by decide) q hq ho factors{r} pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))''')
    if r in [35,45,51,55]:
        emit(f'''  have hfull (q : Nat) (hq : 1 < q) (ho : Odd q) (hb : q ≤ 33) :
      positionTest {r} q (tokenSpec factors{r} pos) = true :=
    positionTest_of_token_cycle (by decide) q hq ho factors{r} pos p
      hfactor hrec (fun i => (hp i).1) (fun i => lt_of_le_of_lt hb (hlarge i))''')
    def projected(_test,q,bullet=True,neutral_spec=None):
        filtered_pairs=', '.join(
            f'({f}, '+('0' if i==j else f'(pos {i}).val')+')'
            for i,f in enumerate(fs) if f % q != 1)
        filtered_spec='['+filtered_pairs+']'
        lead='  · ' if bullet else '  '
        indent='    ' if bullet else '  '
        # Normalize only the token list, keeping the symbolic checker opaque.
        emit(f'''{lead}have hfiltered : projectedTokenSpec {q} factors{r} pos = {filtered_spec} := by
{indent}  change (tokenSpec factors{r} pos).filter (fun tp => decide (tp.1 % {q} ≠ 1)) = {filtered_spec}
{indent}  rw [hspec]
{indent}  norm_num [List.filter_cons, List.filter_nil]
{indent}have hh := hprojected {q} (by decide) (by decide) (by decide)
{indent}rw [hfiltered] at hh''')
        if neutral_spec is None:
            emit(f'{indent}exact hh')
        else:
            emit(f'''{indent}have hneutral : ({neutral_spec} : List (Nat × Nat)).filter
{indent}    (fun tp => decide (tp.1 % {q} ≠ 1)) = {filtered_spec} := by
{indent}  norm_num [List.filter_cons, List.filter_nil]
{indent}have heq := positionTest_filter_ne_one {r} {q} (by decide) {neutral_spec}
{indent}rw [hneutral] at heq
{indent}exact heq.symm.trans hh''')
    def full(test,q):
        emit(f'  · simpa only [{test}, hspec] using\n      hfull {q} (by decide) (by decide) (by decide)')
    if r in [15,21,33,39,57,63]:
        idx={15:[1,2],21:[1],33:[1,3],39:[1],57:[1],63:[1,2]}[r]
        q=33 if r in [15,33] else 3
        emit('  apply exclude'+str(r)+' '+' '.join(f'(pos {i})' for i in idx))
        # This application leaves exactly one goal, so no unnecessary bullet.
        projected(f'test{r}',q,bullet=False)
    elif r==35:
        emit('  apply exclude35 (pos 1) (pos 2) (pos 3) (pos 4)')
        projected('test35_5',5)
        projected('test35_3',3)
        for q in [7,11,13]: full('test35',q)
        emit()
    elif r==45:
        emit('  apply exclude45 (pos 0) (pos 1) (pos 2) (pos 4) (pos 5) (pos 6)')
        projected('test45_3',3)
        spec45='[(3, (pos 0).val), (3, (pos 1).val), (3, (pos 2).val), (11, 0), (19, (pos 4).val)]'
        projected('test45_5',5,neutral_spec=spec45)
        for q in [7,13,19]: full('test45',q)
        emit()
    elif r==51:
        emit('  apply exclude51 (pos 0) (pos 1) (pos 2) (pos 3) (pos 4)')
        projected('test51_3',3)
        projected('test51_7',7)
        for q in [5,11,13]: full('test51',q)
        emit()
    elif r==55:
        emit('  apply exclude55 (pos 1) (pos 2) (pos 3) (pos 4) (pos 5)')
        projected('test55_5',5)
        projected('test55_11',11)
        for q in [3,13,17]: full('test55',q)
        emit()

emit('''end A245211New

/-- The exact second hypothesis of the accepted R2 reduction. -/
theorem OMA.solution : OMA.R_OeisA245211_conjecture_R2.H2 := by
  intro n hs h3 h65 hodd hnp ha
  have hr := A245211New.possible_counts n.primeFactors.card h3 h65 hodd hnp
  rcases hr with h15 | h21 | h33 | h35 | h39 | h45 | h51 | h55 | h57 | h63''')
for r in FACTORS:
    emit(f'  · exact A245211New.no_fixed_count{r} hs h{r} ha')
emit()

path=ROOT/'Main.lean'
path.write_text(''.join(out))
print(f'Wrote {path}: {len(path.read_text().splitlines())} lines')
