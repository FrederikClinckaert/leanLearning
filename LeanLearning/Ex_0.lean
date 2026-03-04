-- OEFENING 1
theorem Ta (a b c d e : Nat)
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d)
    : a = e :=
  calc
      a = b       := h1
    _ = c + 1     := h2
    _ = d + 1     := congrArg Nat.succ h3
    _ = 1 + d     := Nat.add_comm d 1
    _ = e         := Eq.symm h4

-- OEFENING 2
theorem Tb (a b c d : Nat)
    (h1 : a = b + 3)
    (h2 : b = c)
    (h3 : c + 3 = d)
    : a = d :=
  calc
      a = b + 3     := h1
      _ = c + 3     := congrArg (. + 3) h2
      _ = d         := h3

-- OEFENING 3
theorem Tc (a b c d e : Nat)
    (h1 : a = 2 * b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : 2 * (d + 1) = e)
    : a = e :=
  calc
      a = 2 * b       := h1
    _ = 2 * (c + 1)   := congrArg (2 * · ) h2
    _ = 2 * (d + 1)  := congrArg (fun x => 2 * (x + 1)) h3
    _ = e             := h4

-- OEFENING 4
theorem Td (a b c : Nat)
    (h1 : a = b + 2) (h2 : b = c)
    : a = c + 2 :=
  calc
      a = b + 2     := h1
    _ = c + 2       := congrArg (. + 2) h2

-- OEFENING 5
theorem Te (a b c d : Nat)
    (h1 : a = 3 * b)
    (h2 : b = c + 2)
    (h3 : 3 * (c + 2) = d)
    : a = d :=
  calc
    a = 3 * b      := h1
  _ = 3 * (c + 2) := congrArg (fun x => 3 * (x)) h2
  _ = d           := h3

-- OEFENING 6
theorem Tf (a b c d e : Nat)
    (h1 : a = b + 1)
    (h2 : b = 2 * c)
    (h3 : c = d)
    (h4 : 2 * d + 1 = e)
    : a = e :=
  calc
    a = b + 1       := h1
  _ = 2 * c + 1     := congrArg (fun x => x + 1) h2
  _ = 2 * d + 1     := congrArg (fun x => 2 * x + 1) h3
  _ = e             := h4


-- OEFENING 7
theorem Tg (a b c d : Nat)
    (h1 : a = 2 * b + 3)
    (h2 : b = c + 1)
    (h3 : 2 * (c + 1) + 3 = d)
    : a = d :=
  calc
    a = 2 * b + 3         := h1
  _ = 2 * (c + 1) + 3     := congrArg (fun x => 2*x + 3) h2
  _ = d                   := h3

-- OEFENING 8
theorem Th (a b c d : Nat)
    (h1 : a = b + 4)
    (h2 : b = 2 * c)
    (h3 : d = 4 + 2 * c)
    : a = d :=
  calc
      a = b + 4       := h1
    _ = 2 * c + 4     := congrArg (fun x => x + 4) h2
    _ = 4 + 2 * c     := Nat.add_comm (2 * c) 4
    _ = d             := Eq.symm h3

-- OEFENING 9
theorem Ti (a b c d e f : Nat)
    (h1 : a = 3 * b)
    (h2 : b = c + 2)
    (h3 : c = 2 * d)
    (h4 : 3 * (2 * d + 2) = e + 6)
    (h5 : e + 6 = f)
    : a = f :=
  calc
      a = 3 * b               := h1
    _ = 3 * (c+2)             := congrArg (fun x => 3 * x) h2
    _ = 3 * (2 * d + 2)       := congrArg (fun x => 3 * (x + 2)) h3
    _ = e + 6                 := h4
    _ = f                     := h5

-- OEFENING 10
theorem Tj (a b c d e : Nat)
    (h1 : a = b + c)
    (h2 : b = 2 * d)
    (h3 : e = c + 2 * d)
    : a = e :=
  calc
      a = b + c       := h1
    _ = 2 * d + c     := congrArg (fun x => x + c) h2
    _ = c + 2 * d     := Nat.add_comm (2*d) c
    _ = e             := Eq.symm h3

-- OEFENING 11
theorem Tk (a b c d e f : Nat)
    (h1 : a = 2 * b + 1)
    (h2 : b = 3 * c)
    (h3 : c = d + 1)
    (h4 : 3 * (d + 1) = e)
    (h5 : 2 * e + 1 = f)
    : a = f :=
  calc
      a = 2 * b + 1            :=h1
    _ = 2 * (3 * c) + 1        := congrArg (fun x=> 2 * x + 1) h2
    _ = 2 * (3 * (d + 1)) + 1  := congrArg (fun x=> 2 * (3 * x) + 1) h3
    _ = 2 * e + 1              := congrArg (fun x=> 2 * x + 1) h4
    _ = f                      := h5
