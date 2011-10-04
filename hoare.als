sig Hoare {
  pre, post: set Prop,
  prog: Prop -> Prop,
}
{
  -- def. of Hoare triple
  hoare [pre, prog, post]
}
sig Prop {}

-- KAD style definition of Hoare triple
pred hoare (pre: set Prop, prog: Prop -> Prop, post: set Prop) {
  cod[pre.toKA.prog] in post.toKA
}

-- abort: everything goes absurd
sig Abort extends Hoare {}
{
  no prog
}
-- empty program = abort
pred isAbort (h: Hoare) { 
  some h.pre and no h.post
}
run isAbort

abortIsEmpty: check {
  all h: Hoare | isAbort[h] => no h.pre.toKA.(h.prog)
}

-- skip: do nothing
sig Skip extends Hoare {}
{
  prog = Prop.toKA
  pre = post
}

-- Boolean Algebra to Kleene Algebra
fun toKA (p: Prop): Prop -> Prop {
  p <: iden
}

-- order between Hoare triples
pred lte (h1, h2: Hoare) {
  h2.pre in h1.pre
  h1.post in h2.post
}
pred showLte (disj h1, h2: Hoare) {
  lte [h1, h2]
  nonTrivial[h1]
  nonTrivial[h2]
}
run showLte

-- non-trivial triple
pred nonTrivial (h: Hoare) {
  some h.pre.toKA & dom[h.prog]
}
run nonTrivial

-- structural rules

-- sequential composition
fun next (h1, h2: Hoare): Hoare {
  { h: Hoare {
    h.pre = h1.pre 
    h.post = h2.post
    h.prog = (h1.prog).(h2.prog)
  }}
}
pred isNext (disj h, h1, h2: Hoare) {
  h = h1.next[h2]
  some h.pre
  some h.prog
  h not in h1 + h2
}
run isNext for 5

-- condition
fun if (b: set Prop, thn, els: Hoare): Hoare {
  { h: Hoare {
    -- then clause
    thn.pre = b & h.pre
    thn.post = h.post
    -- else clause
    els.pre = neg[b] & h.pre
    els.post = h.post
    -- program
    h.prog = (b.toKA).(thn.prog) + (neg[b].toKA).(els.prog)
  }}
}
pred isIf (disj h, thn, els: Hoare) {
  some b: Prop | h = if [b, thn, els]
  nonTrivial[h]
  nonTrivial[thn]
  nonTrivial[els]
}
run isIf

-- while loop (for partial model)
fun while (b: set Prop, inner: Hoare): Hoare {
  { h: Hoare {
    -- precondition
    inner.pre = h.pre & b
    -- postcondition
    inner.post = h.pre
    h.post = inner.post & neg[b]

    -- relational model
    h.prog = *((b.toKA).(inner.prog)).(neg[b].toKA)
  }}
}
pred showWhile (b: set Prop, h, hw: Hoare) {
  hw = while [b, h]
  nonTrivial[h]
  nonTrivial[hw]
}
run showWhile for 5

-- Expand a while-loop once 
expandWhileOnce: check {
  all b: Prop, h: Hoare | 
    let w = while [b, h] | 
    let w' = if [b, h.next[w], Skip] | 
      hoare [w.pre, w'.prog, w.post] and hoare [w'.pre, w.prog, w'.post]
} for 6

-- negation
fun neg (b: Prop): Prop {
  Prop - b
}

-- lemmas ([Moeller&Struth03] Lemma 6.1)
lemma_i: check {
  all h: Hoare |
    h.pre.toKA.(h.prog) = h.prog.(h.pre.toKA) => hoare[h.pre, h.prog, h.post]
} for 10
lemma_ii: check {
  all h1, h2: Hoare | 
    h1.pre = h2.pre => hoare[h1.pre, h1.prog + h2.prog, h1.post + h2.post]
} for 10
lemma_iii: check {
  all h1, h2: Hoare | 
    h1.post = h2.post and h1.prog = h2.prog
      => hoare[h1.pre + h2.pre, h1.prog, h1.post]  
} for 10
lemma_iv: check {
  all h1, h2: Hoare | 
    h1.prog = h2.prog => hoare[h1.pre & h2.pre, h1.prog, h1.post & h2.post] 
} for 10
lemma_v: check {
  all h: Hoare, p: Prop |
    p.toKA.(h.prog) = h.prog.(p.toKA) => hoare [p & h.pre, h.prog, p & h.post]
} for 10

-- (liberal) weakest precondition
fun wlp(h: Hoare): set iden {
  dom[neg[h.prog.(neg[h.post])].toKA]
}
run wlp

wlpMeets: check {
  all h: Hoare | no wlp[h].(h.prog).(neg[h.post])
} for 10
wlpIsReallyWeak: check {
  all h: Hoare | h.pre.toKA in wlp[h]
} for 10

-- domain
fun dom (r: univ -> univ): univ -> univ {
  r.univ <: iden
}
run dom

-- codomain
fun cod (r: univ -> univ): univ -> univ {
  dom[~r]
}

-- definitions of domain
defOfDomain1: check {
  all a: univ -> univ | a in dom[a].a
}
defOfDomain2: check {
  all a: univ -> univ, p: set iden | dom[p.a] in p  
}
defOfDomain3: check { -- additional, locality
  all a, b: univ -> univ | dom[a.(dom[b])] in dom[a.b]
}

--properties of domain
strictness: check {
  all a: univ -> univ | no dom[a] iff no a
}
additivity: check {
  all a, b: univ -> univ | dom[a+b] = dom[a] + dom[b]
}
monotonicity: check {
  all a, b: univ -> univ | a in b => dom[a] in dom[b]
}
decomposition: check {
  all a, b: univ -> univ | dom[a.b] in dom[a.(dom[b])]
}
import_export: check {
  all a: univ -> univ, p: set iden |  dom[p.a] = p.(dom[a])
}
stability: check {
  all p: set iden | dom[p] = p
}
induction: check {
  all a: univ -> univ, p: set iden | dom[a.p] in p => dom[*a.p] in p
}
