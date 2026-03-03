theorem T (a b c d e : Nat)
    (h1 : a = b) (h2 : b = c + 1) (h3 : c = d) (h4 : e = 1 + d)
    : a = e :=
  calc
      a = b       := h1
    _ = c + 1     := h2
    _ = d + 1     := congrArg Nat.succ h3
    _ = 1 + d     := Nat.add_comm d 1
    _ = e         := Eq.symm h4
