open util/relation

some sig Hoare {
  pre: set Prop,
  prog: Prop -> Prop,
  post: set Prop
}
{
  some prog
  all p: pre | some q: post | p.prog in q
}

sig A, B extends Prop {}
sig Prop extends Kleene {
}
abstract sig Kleene {}

run { #pre > 2  } for 5

fun sigma (r: Prop -> Prop): Prop {
  r.Prop
}

-- properties of domain 
check {
  -- strictness
  all h: Hoare | no dom[h.prog]  <=> no h.prog
  -- addivity
  all h1, h2: Hoare | dom[h1.prog + h2.prog] = dom[h1.prog] + dom[h2.prog]
  -- monotonicity
  all h1, h2: Hoare | h1.prog in h2.prog => dom[h1.prog] in dom[h2.prog]
  -- decomposition
--  all h1, h2: Hoare | dom[h1.prog.(h2.prog)] in dom[h1.prog.(dom[h2.prog])]  

}
