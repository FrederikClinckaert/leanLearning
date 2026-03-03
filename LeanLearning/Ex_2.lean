theorem T (a b c d e : Nat)
    (h1 : a = 2 * b) (h2 : b = c + 1) (h3 : c = d) (h4 : 2 * (d + 1) = e)
    : a = e :=
  calc
      a = 2 * b       := h1
    _ = 2 * (c + 1)   := congrArg (2 * · ) h2
    _ = 2 * (d + 1)  := congrArg (fun x => 2 * (x + 1)) h3
    _ = e             := h4
