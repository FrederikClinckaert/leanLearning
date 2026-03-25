--VOORBEELD:
theorem voorbeeld_apply (P Q R : Prop)
    (h1 : P → Q)   -- Als P, dan Q
    (h2 : Q → R)   -- Als Q, dan R
    (hp : P)       -- P is waar
    : R :=         -- Ons doel is R
by
  -- Ons doel is nu R.
  -- Hypothese h2 eindigt in R. We passen deze toe "van achteren naar voren".
  apply h2

  -- Ons doel is nu veranderd in Q!
  -- Hypothese h1 eindigt in Q.
  apply h1

  -- Ons doel is nu veranderd in P!
  -- We hebben al een hypothese 'hp' die exact P is.
  exact hp

-- OEFENING 1
theorem Tl(A B C D E : Prop)
    (h1 : A → B)
    (h2 : B → C)
    (h3 : C → D)
    (h4 : D → E)
    (ha : A)
    : E :=
by
  apply h4
  apply h3
  apply h2
  apply h1
  apply ha

-- OEFENING 2
theorem Tm (n m : Nat)
    (h1 : n = m → n + 1 = m + 1)  -- Als n=m, dan n+1=m+1
    (h2 : n = 0 → n = m)          -- Als n=0, dan n=m
    (hn : n = 0)                  -- n is 0
    : n + 1 = m + 1 :=
by
  apply h1
  apply h2
  apply hn
