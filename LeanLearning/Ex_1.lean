theorem T (a b c d : Nat)
    (h1 : a = b + 3) (h2 : b = c) (h3 : c + 3 = d)
    : a = d :=
  calc
      a = b + 3     := h1
      _ = c + 3     := congrArg (. + 3) h2
      _ = d         := h3
