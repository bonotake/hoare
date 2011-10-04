some sig Hoare {
  pre, post: set Prop,
  prog: Prop -> Prop,
}
{
  -- def. of Hoare triple
  all p: pre | p.prog in post
}
sig Prop {}

-- abort: everything goes absurd
sig Abort extends Hoare {}
{
  no prog
}

-- skip: do nothing
sig Skip extends Hoare {}
{
  prog = Prop.toKA
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
      h.pre = b & h.post
        => all p: h.post | p.(w'.prog) in neg[b] & h.post
}

-- negation
fun neg (b: Prop): Prop {
  Prop - b
}

-- test run
pred show(h: Hoare) {
  some p: Prop | p.(h.prog) in (h.post) and some p.(h.prog) and p not in h.pre
}
run show
run { some h: Hoare | some h.prog and some (Prop - h.post) and some h.post }

-- empty program = abort
pred isAbort (h: Hoare) { 
  some pre and no post
}
run isAbort

abortIsEmpty: check {
  all h: Hoare | isAbort[h] => (no h.pre & h.prog.univ or no h.prog)
}

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
