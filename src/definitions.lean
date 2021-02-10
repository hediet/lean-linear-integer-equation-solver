import data.bool
import data.int.gcd

def rdiv (as: list ℤ) (f: ℤ): list ℤ := as.map (λ a, a / f)
def rmul (as: list ℤ) (f: ℤ): list ℤ := as.map (λ a, a * f)

def smul (as bs: list ℤ): ℤ := ((as.zip bs).map (λ (t: ℤ × ℤ), t.1 * t.2)).foldr (+) 0

def gcd_list: list ℤ → ℕ
| [] := 0
| [x] := x.nat_abs
| (x :: xs) := nat.gcd x.nat_abs (gcd_list xs)

def xgcd_list: list ℤ → list ℤ
| [] := []
| [x] := [if x < 0 then -1 else 1]
| (x :: xs) :=
	(if x < 0 then -1 else 1) * nat.gcd_a x.nat_abs (gcd_list xs)
	:: rmul (xgcd_list xs) (nat.gcd_b x.nat_abs (gcd_list xs))

def to_subscript : char → char
| '0' := '₀'
| '1' := '₁'
| '2' := '₂'
| '3' := '₃'
| '4' := '₄'
| '5' := '₅'
| '6' := '₆'
| '7' := '₇'
| '8' := '₈'
| '9' := '₉'
| c := c

def repr_subscript : ℕ → string
| n := ((repr n).to_list.map to_subscript).as_string

structure Eq := mk :: (as : list ℤ) (c: ℤ)

instance : has_repr Eq :=
⟨ λ eq, (string.join ((eq.as.map_with_index (λ i a,  repr a ++ "x" ++ repr_subscript i)).intersperse " + ")) ++ " = " ++ (repr eq.c) ⟩

instance : inhabited Eq :=
⟨ Eq.mk [] 0 ⟩

def Eq.is_solution (eq: Eq) (xs: list ℤ): bool :=
	(xs.length = eq.as.length) && (smul eq.as xs = eq.c)

instance : has_mem (list ℤ) Eq := ⟨ λ s eq, eq.is_solution s ⟩

def Eq.has_solution (eq: Eq): bool := (gcd_list eq.as) ∣ eq.c.nat_abs

def Eq.get_solution (eq: Eq) : option (list ℤ) :=
	if eq.has_solution
	then some (rmul (xgcd_list eq.as) (if eq.c = 0 then 0 else (eq.c / gcd_list eq.as)))
	else none

def Eq.mul (e: Eq) (f: ℤ) := Eq.mk (rmul e.as f) (e.c * f)
def Eq.div (e: Eq) (f: ℤ) := Eq.mk (rdiv e.as f) (e.c / f)
def Eq.add (e e2: Eq) := Eq.mk ((e.as.zip e2.as).map (λ ⟨ a, b ⟩, a + b )) (e.c + e2.c)


def Eq.remove_column (eq: Eq) (col: ℕ): Eq := Eq.mk (eq.as.remove_nth col) eq.c
def Eq.insert_column (eq: Eq): Eq := Eq.mk (0::eq.as) eq.c

def Eq.is_zero (e: Eq): bool := (e.as.all (=0)) && (e.c = 0)

def Eq.equiv (eq1 eq2: Eq): Prop := ∀ xs: list ℤ, xs ∈ eq1 ↔ xs ∈ eq2




structure Eqs := (dim: ℕ) (eqs : list Eq)

instance : has_repr Eqs :=
⟨ λ eqs, string.join ((eqs.eqs.map repr).intersperse "\n") ⟩

def Eqs.is_solution (e: Eqs) (xs: list ℤ): bool := (xs.length = e.dim) && e.eqs.all (λ eq, eq.is_solution xs)


def Eqs.from (eqs: list Eq): Eqs := ⟨ (eqs.head'.map (λ (h: Eq), h.as.length)).get_or_else 0, eqs ⟩

instance : has_mem (list ℤ) Eqs := ⟨ λ s eq, eq.is_solution s ⟩


def Eqs.equiv (e1 e2: Eqs): Prop := ∀ xs: list ℤ, xs ∈ e1 ↔ xs ∈ e2


def Eqs.indexed_coefficients (e: Eqs): list (ℤ × ℕ × ℕ) :=
	(e.eqs.map_with_index (λ idx1 (eq: Eq), 
		eq.as.map_with_index (λ idx2 v, (v, idx1, idx2))
	)).join

def Eqs.remove_column (eqs: Eqs) (col: ℕ): Eqs := Eqs.mk (eqs.dim - 1) (eqs.eqs.map (λ eq, eq.remove_column col))
def Eqs.insert_column (eqs: Eqs): Eqs := Eqs.mk (eqs.dim + 1) (eqs.eqs.map (λ eq, eq.insert_column))

def Eqs.cons_eq (e: Eqs) (eq: Eq): Eqs := Eqs.mk e.dim (eq::e.eqs)
