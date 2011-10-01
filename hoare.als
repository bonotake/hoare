some sig Hoare {
  pre, post: set Prop,
  prog: pre -> post,
}
{
  all p: pre | p.prog in post
}

sig Prop {}
sig A, B, C extends Prop {}

fun dom (r: univ -> univ): univ -> univ {
  r.univ <: iden
}

run {some prog #pre > 2 }

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
--  all a: A -> B, b: B -> C | dom[a.b] in dom[a.(dom[b])]
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
