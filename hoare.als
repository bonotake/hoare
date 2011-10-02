some sig Hoare {
  pre, post: set Prop,
  prog: Prop -> Prop,
}
{
  -- def. of Hoare triple
  all p: pre | p.prog in post
}
sig Prop {}

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
  dom[(Prop - (h.prog.(Prop - h.post))) <: iden]
}
run wlp

wlpMeets: check {
  all h: Hoare | no wlp[h].(h.prog).(Prop - h.post)
} for 10
wlpIsReallyWeak: check {
  all h: Hoare | h.pre in wlp[h].univ
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
