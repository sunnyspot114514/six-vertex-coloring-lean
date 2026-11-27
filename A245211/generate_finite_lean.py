"""Generate kernel-checked finite residue lemmas; Python supplies no proofs.

Run position_certificates.py first. The emitted closed propositions are all
proved using Lean's `decide +kernel`, including completeness of every table.
"""
from pathlib import Path
import json

ROOT = Path(__file__).parent
DATA = json.loads((ROOT / 'position_certificates.json').read_text())
out = []

def emit(text=''):
    out.append(text.rstrip() + '\n')

def form(name, rows):
    width = len(rows[0])
    typ = ' × '.join(['Nat'] * width)
    literals = ',\n    '.join('(' + ', '.join(map(str,row)) + ')' for row in rows)
    emit(f'def {name} (i : Fin {len(rows)}) : {typ} :=\n'
         f'  ([{literals}] : List ({typ}))[i.val]!\n')

def spec(tokens):
    return '[' + ', '.join(f'({f}, {p})' for f,p in tokens) + ']'

def representatives(rows, repeated):
    seen = {}
    result = []
    for i, row in enumerate(rows):
        key = tuple(sorted(row[:repeated]) + row[repeated:])
        seen.setdefault(key, i)
        result.append(seen[key])
    return result

def abbrev(name, r, q, params, tokens):
    bind = f' ({" ".join(params)} : Nat)' if params else ''
    emit(f'abbrev {name}{bind} : Bool :=\n  positionTest {r} {q} {spec(tokens)}\n')

def closed(name, statement, private=True):
    emit(f'{"private " if private else ""}theorem {name} :\n    {statement} := by\n  decide +kernel\n')

def glue(name, param, size, statement, blocks, private=True):
    emit(f'{"private " if private else ""}theorem {name} ({param} : Fin {size}) :\n    {statement} := by\n  fin_cases {param}')
    for block in blocks:
        emit(f'  · simpa using {block}')
    emit()

def split_guarded(name, param, size, tail, width=None, intervals=None):
    """Bound each kernel computation without changing its public proposition."""
    if intervals is None:
        intervals = [(lo, min(lo + width, size)) for lo in range(0, size, width)]
    for k, (lo, hi) in enumerate(intervals):
        closed(f'{name}_slice{k}',
               f'∀ {param} : Fin {size}, {lo} ≤ {param}.val → {param}.val < {hi} →\n      '+tail)
    emit(f'private theorem {name} ({param} : Fin {size}) :\n    {tail} := by\n'
         f'  have hbound := {param}.isLt')
    for k, (_, hi) in enumerate(intervals[:-1]):
        emit(f'  by_cases h{k} : {param}.val < {hi}\n'
             f'  · exact {name}_slice{k} {param} (by omega) h{k}')
    emit(f'  exact {name}_slice{len(intervals)-1} {param} (by omega) (by omega)\n')

emit('''import A245211.Projection

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
''')

emit('/-! ## Six small cases -/\n')
tiny = [
 (15,33,['a','b'],[(3,'0'),(3,'a'),(11,'b')]),
 (21,3,['a'],[(3,'0'),(3,'a')]),
 (33,33,['a','b'],[(3,'0'),(3,'a'),(683,'b')]),
 (39,3,['a'],[(3,'0'),(3,'a')]),
 (57,3,['a'],[(3,'0'),(3,'a')]),
 (63,3,['a','b'],[(3,'0'),(3,'a'),(3,'b')]),
]
for r,q,params,tokens in tiny:
    abbrev(f'test{r}',r,q,params,tokens)
    vs = ' '.join(params)
    args = ' '.join(f'{v}.val' for v in params)
    closed(f'exclude{r}',f'∀ {vs} : Fin {r}, test{r} {args} = true → False',False)

emit('/-! ## Thirty-five factors -/\n')
abbrev('test35_5',35,5,['a'],[(3,'0'),(43,'a')])
abbrev('test35_3',35,3,['b','c','d'],[(3,'0'),(11,'b'),(281,'c'),(86171,'d')])
abbrev('test35',35,'q',['q','b','a','c','d'],[(3,'0'),(11,'b'),(43,'a'),(281,'c'),(86171,'d')])
closed('classify35_5','∀ a : Fin 35, test35_5 a.val = true → a.val = 1 ∨ a.val = 34')
def shape35(b,c,d):
    return f'({b} = 1 ∧ {c} = {d}) ∨\n      ({c} = 1 ∧ {b} = {d}) ∨ ({d} = 1 ∧ {b} = {c})'
for k in range(35):
    closed(f'classify35_3_block{k}',
           f'∀ c d : Fin 35, test35_3 {k} c.val d.val = true →\n      '+shape35(str(k),'c.val','d.val'))
glue('classify35_3','b',35,
     '∀ c d : Fin 35, test35_3 b.val c.val d.val = true →\n      '+shape35('b.val','c.val','d.val'),
     [f'classify35_3_block{k}' for k in range(35)])
for k,vars_ in enumerate([('1','t.val','t.val'),('t.val','1','t.val'),('t.val','t.val','1')]):
    b,c,d=vars_
    closed(f'exclude35_pattern{k}',
           '∀ a t : Fin 35, (a.val = 1 ∨ a.val = 34) →\n      '+
           '\n      '.join(f'test35 {q} {b} a.val {c} {d} = true →' for q in [7,11,13])+'\n      False')
emit('''theorem exclude35 (b a c d : Fin 35)
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
''')

emit('/-! ## Forty-five factors -/\n')
form('forms45_3',DATA['45']['stage1_normal_forms'])
form('forms45_5',DATA['45']['stage2_normal_forms'])
abbrev('test45_3',45,3,['a','b','c'],[(3,'a'),(3,'b'),(3,'c'),(11,'0')])
abbrev('test45_5',45,5,['a','b','c','d'],[(3,'a'),(3,'b'),(3,'c'),(11,'0'),(19,'d')])
abbrev('test45_7',45,7,['a','b','c','d','e'],[(3,'a'),(3,'b'),(3,'c'),(11,'0'),(19,'d'),(331,'e')])
abbrev('test45',45,'q',['q','a','b','c','d','e','f'],[(3,'a'),(3,'b'),(3,'c'),(11,'0'),(19,'d'),(331,'e'),(18837001,'f')])
emit('''private theorem test45_neutral (a b c d e f : Nat) :
    test45 7 a b c d e f = test45_7 a b c d e := by
  exact positionTest_append_mod_one 45 7 (by decide)
    [(3, a), (3, b), (3, c), (11, 0), (19, d), (331, e)] []
    (18837001, f) (by change 18837001 % 7 = 1; decide)
''')
def eq45_3(a,b,c):
    return (f'∃ i : Fin 13, {a} = (forms45_3 i).1 ∧\n'
            f'        {b} = (forms45_3 i).2.1 ∧ {c} = (forms45_3 i).2.2')
for k in range(45):
    closed(f'classify45_3_block{k}',
           f'∀ b c : Fin 45, test45_3 {k} b.val c.val = true →\n      '+eq45_3(str(k),'b.val','c.val'))
glue('classify45_3','a',45,
     '∀ b c : Fin 45, test45_3 a.val b.val c.val = true →\n      '+eq45_3('a.val','b.val','c.val'),
     [f'classify45_3_block{k}' for k in range(45)])
closed('classify45_5','''∀ (i : Fin 13) (d : Fin 45),
      test45_5 (forms45_3 i).1 (forms45_3 i).2.1 (forms45_3 i).2.2 d.val = true →
      ∃ j : Fin 13, (forms45_3 i).1 = (forms45_5 j).1 ∧
        (forms45_3 i).2.1 = (forms45_5 j).2.1 ∧
        (forms45_3 i).2.2 = (forms45_5 j).2.2.1 ∧
        d.val = (forms45_5 j).2.2.2''')
def tail45(i):
    vals = ' '.join(f'(forms45_5 {i}){projection}' for projection in ['.1','.2.1','.2.2.1','.2.2.2'])
    return (f'test45_7 {vals} e.val = true →\n      ∀ f : Fin 45,\n      '+
            '\n      '.join(f'test45 {q} {vals} e.val f.val = true →' for q in [13,19])+ '\n      False')
def final45(i):
    return '∀ e : Fin 45,\n      '+tail45(i)
rows45 = DATA['45']['stage2_normal_forms']
for k, representative in enumerate(representatives(rows45, 3)):
    if k == representative:
        split_guarded(f'exclude45_forms_block{k}', 'e', 45, tail45(f'({k} : Fin 13)'), 9)
    else:
        row, target = rows45[k], rows45[representative]
        prefix = spec([(3,x) for x in row[:3]])
        target_prefix = spec([(3,x) for x in target[:3]])
        suffix7 = spec([(11,0),(19,row[3]),(331,'e.val')])
        suffix = spec([(11,0),(19,row[3]),(331,'e.val'),(18837001,'f.val')])
        emit(f'private theorem exclude45_forms_block{k} :\n    {final45(f"({k} : Fin 13)")} := by\n'
             '  intro e h7 f h13 h19\n'
             f'  have hperm : List.Perm {prefix} {target_prefix} := by decide\n'
             f'  have ht7 : test45_7 {" ".join(map(str,row))} e.val =\n'
             f'      test45_7 {" ".join(map(str,target))} e.val :=\n'
             f'    positionTest_perm 45 7 (List.Perm.append_right {suffix7} hperm)\n'
             f'  have htest (q : Nat) : test45 q {" ".join(map(str,row))} e.val f.val =\n'
             f'      test45 q {" ".join(map(str,target))} e.val f.val := by\n'
             f'    exact positionTest_perm 45 q (List.Perm.append_right {suffix} hperm)\n'
             f'  exact exclude45_forms_block{representative} e (ht7.symm.trans h7) f\n'
             '    ((htest 13).symm.trans h13) ((htest 19).symm.trans h19)\n')
glue('exclude45_forms','j',13,final45('j'),[f'exclude45_forms_block{k}' for k in range(13)])
emit('''theorem exclude45 (a b c d e f : Fin 45)
    (h3 : test45_3 a.val b.val c.val = true)
    (h5 : test45_5 a.val b.val c.val d.val = true)
    (h7 : test45 7 a.val b.val c.val d.val e.val f.val = true)
    (h13 : test45 13 a.val b.val c.val d.val e.val f.val = true)
    (h19 : test45 19 a.val b.val c.val d.val e.val f.val = true) : False := by
  have h7' : test45_7 a.val b.val c.val d.val e.val = true :=
    (test45_neutral a.val b.val c.val d.val e.val f.val).symm.trans h7
  obtain ⟨i, ha, hb, hc⟩ := classify45_3 a b c h3
  obtain ⟨j, hja, hjb, hjc, hjd⟩ := classify45_5 i d
    (by simpa only [ha, hb, hc] using h5)
  exact exclude45_forms j e
    (by simpa only [ha, hb, hc, hja, hjb, hjc, hjd] using h7') f
    (by simpa only [ha, hb, hc, hja, hjb, hjc, hjd] using h13)
    (by simpa only [ha, hb, hc, hja, hjb, hjc, hjd] using h19)
''')

emit('/-! ## Fifty-one factors -/\n')
form('forms51_3',DATA['51']['stage1_normal_forms'])
abbrev('test51_3',51,3,['a','b'],[(3,'a'),(3,'b'),(43691,'0')])
abbrev('test51_7',51,7,['a','b','c','e'],[(3,'a'),(3,'b'),(307,'c'),(6529,'e'),(43691,'0')])
abbrev('test51',51,'q',['q','a','b','c','d','e'],[(3,'a'),(3,'b'),(307,'c'),(2857,'d'),(6529,'e'),(43691,'0')])
for k in range(51):
    closed(f'classify51_3_block{k}',
           f'∀ b : Fin 51, test51_3 {k} b.val = true →\n'
           f'      ∃ i : Fin 3, {k} = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2')
glue('classify51_3','a',51,
     '∀ b : Fin 51, test51_3 a.val b.val = true →\n'
     '      ∃ i : Fin 3, a.val = (forms51_3 i).1 ∧ b.val = (forms51_3 i).2',
     [f'classify51_3_block{k}' for k in range(51)])
def body51(i, c):
    a,b=f'(forms51_3 {i}).1',f'(forms51_3 {i}).2'
    return (f'test51_7 {a} {b} {c} e.val = true →\n'
            '      ∀ d : Fin 51,\n      '+
            '\n      '.join(f'test51 {q} {a} {b} {c} d.val e.val = true →' for q in [5,11,13])+'\n      False')
def tail51(i, c):
    return '∀ e : Fin 51, '+body51(i, c)
def final51(i):
    return '∀ c : Fin 51,\n      '+tail51(i, 'c.val')
rows51 = DATA['51']['stage1_normal_forms']
for k, representative in enumerate(representatives(rows51, 2)):
    if k == representative:
        for c in range(51):
            live = sorted(row[3] for row in DATA['51']['stage2_normal_forms']
                          if row[:3] == rows51[k] + [c])
            if len(live) <= 8:
                closed(f'exclude51_forms_block{k}_slot{c}', tail51(f'({k} : Fin 3)', str(c)))
            else:
                cuts = [0] + [live[j] + 1 for j in range(7, len(live)-1, 8)] + [51]
                intervals = list(zip(cuts, cuts[1:]))
                split_guarded(f'exclude51_forms_block{k}_slot{c}', 'e', 51,
                              body51(f'({k} : Fin 3)', str(c)), intervals=intervals)
        glue(f'exclude51_forms_block{k}', 'c', 51, tail51(f'({k} : Fin 3)', 'c.val'),
             [f'exclude51_forms_block{k}_slot{c}' for c in range(51)])
    else:
        row, target = rows51[k], rows51[representative]
        prefix = spec([(3,x) for x in row])
        target_prefix = spec([(3,x) for x in target])
        suffix7 = spec([(307,'c.val'),(6529,'e.val'),(43691,0)])
        suffix = spec([(307,'c.val'),(2857,'d.val'),(6529,'e.val'),(43691,0)])
        emit(f'private theorem exclude51_forms_block{k} :\n    {final51(f"({k} : Fin 3)")} := by\n'
             '  intro c e h7 d h5 h11 h13\n'
             f'  have hperm : List.Perm {prefix} {target_prefix} := by decide\n'
             f'  have ht7 : test51_7 {" ".join(map(str,row))} c.val e.val =\n'
             f'      test51_7 {" ".join(map(str,target))} c.val e.val :=\n'
             f'    positionTest_perm 51 7 (List.Perm.append_right {suffix7} hperm)\n'
             f'  have htest (q : Nat) : test51 q {" ".join(map(str,row))} c.val d.val e.val =\n'
             f'      test51 q {" ".join(map(str,target))} c.val d.val e.val :=\n'
             f'    positionTest_perm 51 q (List.Perm.append_right {suffix} hperm)\n'
             f'  exact exclude51_forms_block{representative} c e (ht7.symm.trans h7) d\n'
             '    ((htest 5).symm.trans h5) ((htest 11).symm.trans h11) ((htest 13).symm.trans h13)\n')
glue('exclude51_forms','i',3,final51('i'),[f'exclude51_forms_block{k}' for k in range(3)])
emit('''theorem exclude51 (a b c d e : Fin 51)
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
''')

emit('/-! ## Fifty-five factors -/\n')
form('forms55_11',DATA['55']['stage2_normal_forms'])
abbrev('test55_5',55,5,['a'],[(3,'0'),(683,'a')])
abbrev('test55_11',55,11,['b','c'],[(3,'0'),(11,'b'),(11,'c')])
abbrev('test55_3',55,3,['b','c','a','e'],[(3,'0'),(11,'b'),(11,'c'),(683,'a'),(48912491,'e')])
abbrev('test55',55,'q',['q','b','c','a','d','e'],[(3,'0'),(11,'b'),(11,'c'),(683,'a'),(2971,'d'),(48912491,'e')])
emit('''private theorem test55_neutral (b c a d e : Nat) :
    test55 3 b c a d e = test55_3 b c a e := by
  exact positionTest_append_mod_one 55 3 (by decide)
    [(3, 0), (11, b), (11, c), (683, a)] [(48912491, e)]
    (2971, d) (by change 2971 % 3 = 1; decide)
''')
closed('classify55_5','∀ a : Fin 55, test55_5 a.val = true → a.val = 1 ∨ a.val = 54')
for k in range(55):
    closed(f'classify55_11_block{k}',
           f'∀ c : Fin 55, test55_11 {k} c.val = true →\n'
           f'      ∃ i : Fin 19, {k} = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2')
glue('classify55_11','b',55,
     '∀ c : Fin 55, test55_11 b.val c.val = true →\n'
     '      ∃ i : Fin 19, b.val = (forms55_11 i).1 ∧ c.val = (forms55_11 i).2',
     [f'classify55_11_block{k}' for k in range(55)])
def tail55(i,a):
    b,c=f'(forms55_11 {i}).1',f'(forms55_11 {i}).2'
    return (f'test55_3 {b} {c} {a} e.val = true →\n      ∀ d : Fin 55,\n      '+
            '\n      '.join(f'test55 {q} {b} {c} {a} d.val e.val = true →' for q in [13,17])+'\n      False')
def final55(i,a):
    return '∀ e : Fin 55,\n      '+tail55(i,a)
for a in [1,54]:
    rows55 = DATA['55']['stage2_normal_forms']
    for k, representative in enumerate(representatives(rows55, 2)):
        if k == representative:
            closed(f'exclude55_a{a}_block{k}', final55(f'({k} : Fin 19)',a))
        else:
            row, target = rows55[k], rows55[representative]
            prefix = spec([(11,x) for x in row])
            target_prefix = spec([(11,x) for x in target])
            suffix3 = spec([(683,a),(48912491,'e.val')])
            suffix = spec([(683,a),(2971,'d.val'),(48912491,'e.val')])
            emit(f'private theorem exclude55_a{a}_block{k} :\n    {final55(f"({k} : Fin 19)",a)} := by\n'
                 '  intro e h3 d h13 h17\n'
                 f'  have hperm : List.Perm {prefix} {target_prefix} := by decide\n'
                 f'  have ht3 : test55_3 {" ".join(map(str,row))} {a} e.val =\n'
                 f'      test55_3 {" ".join(map(str,target))} {a} e.val :=\n'
                 f'    positionTest_perm 55 3 (List.Perm.cons (3, 0) (List.Perm.append_right {suffix3} hperm))\n'
                 f'  have htest (q : Nat) : test55 q {" ".join(map(str,row))} {a} d.val e.val =\n'
                 f'      test55 q {" ".join(map(str,target))} {a} d.val e.val := by\n'
                 f'    exact positionTest_perm 55 q (List.Perm.cons (3, 0) (List.Perm.append_right {suffix}\n'
                 f'      hperm))\n'
                 f'  exact exclude55_a{a}_block{representative} e (ht3.symm.trans h3) d\n'
                 '    ((htest 13).symm.trans h13) ((htest 17).symm.trans h17)\n')
    glue(f'exclude55_a{a}','i',19,final55('i',a),[f'exclude55_a{a}_block{k}' for k in range(19)])
emit('''theorem exclude55 (b c a d e : Fin 55)
    (h5 : test55_5 a.val = true)
    (h11 : test55_11 b.val c.val = true)
    (h3 : test55 3 b.val c.val a.val d.val e.val = true)
    (h13 : test55 13 b.val c.val a.val d.val e.val = true)
    (h17 : test55 17 b.val c.val a.val d.val e.val = true) : False := by
  have h3' : test55_3 b.val c.val a.val e.val = true :=
    (test55_neutral b.val c.val a.val d.val e.val).symm.trans h3
  obtain ⟨i, hb, hc⟩ := classify55_11 b c h11
  rcases classify55_5 a h5 with ha | ha
  · exact exclude55_a1 i e
      (by simpa only [hb, hc, ha] using h3') d
      (by simpa only [hb, hc, ha] using h13)
      (by simpa only [hb, hc, ha] using h17)
  · exact exclude55_a54 i e
      (by simpa only [hb, hc, ha] using h3') d
      (by simpa only [hb, hc, ha] using h13)
      (by simpa only [hb, hc, ha] using h17)

end A245211New
''')

path = ROOT / 'Finite.lean'
path.write_text(''.join(out))
print(f'Wrote {path}: {len(path.read_text().splitlines())} lines')
