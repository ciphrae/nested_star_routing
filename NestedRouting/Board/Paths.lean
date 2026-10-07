import NestedRouting.Board.Basic

/-! Legal paths, reachability from the target, and the optimal solution length
`optimalLength` with a shortest witness. -/

namespace SlidingPuzzle

variable {n : ℕ} [NeZero n]

/-- A finite legal walk, with endpoints in its type. -/
inductive Path : Board n → Board n → Type
  | nil (B : Board n) : Path B B
  | cons {A B C : Board n} (step : Step A B) (tail : Path B C) : Path A C

namespace Path

variable {A B C : Board n}

def length {A B : Board n} : Path A B → ℕ
  | .nil _ => 0
  | .cons _ p => p.length + 1

@[simp] theorem length_nil (B : Board n) : (nil B).length = 0 := rfl
@[simp] theorem length_cons {A B C : Board n} (h : Step A B) (p : Path B C) :
    (cons h p).length = p.length + 1 := rfl

def append {A B C : Board n} (p : Path A B) (q : Path B C) : Path A C :=
  match p with
  | .nil _ => q
  | .cons h p => .cons h (p.append q)

@[simp] theorem length_append (p : Path A B) (q : Path B C) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [append]
  | cons h p ih => simp [append, ih, Nat.add_assoc, Nat.add_comm]

def reverse {A B : Board n} (p : Path A B) : Path B A :=
  match p with
  | .nil _ => .nil _
  | .cons h p => p.reverse.append (.cons h.symm (.nil _))

@[simp] theorem length_reverse (p : Path A B) : p.reverse.length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [reverse, ih]

end Path

/-- The orbit is defined by actual paths, not a distance default on disconnected states. -/
def Reachable (B : Board n) : Prop := Nonempty (Path (target n) B)

end SlidingPuzzle
