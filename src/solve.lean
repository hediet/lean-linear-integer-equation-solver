import .definitions
import data.bool
import data.int.gcd
import tactic
import .mod

def find_isolated_var (e: Eqs): option (ℕ × ℕ) :=
	let
		indices := e.indexed_coefficients,
		ones := indices.filter (λ t, t.fst.nat_abs = 1),
		indices := ones.map (λ t, t.snd)
	in
		indices.head'

def find_min_non_zero_or_default (e: Eqs): option (ℕ × ℕ) :=
	let
		indices := e.indexed_coefficients,
		non_negative := indices.filter (λ t, t.fst ≠ 0),
		min := non_negative.argmin (λ t, t.fst.nat_abs)
	in
		(min.map (λ t, t.snd))


def annihilate_var (e: Eq) (var_def: Eq) (i: ℕ): Eq :=
	e.add (var_def.mul (e.as.inth i / var_def.as.inth i * -1))


def mapM {α: Type}: list (option α) → option (list α)
| [] := some []
| ((some a)::as) := (mapM as).map (λ bs, a :: bs)
| (none::as) := none


structure EqsReduction := (eqs: Eqs) (reduction: list ℤ → list ℤ)

instance : has_repr EqsReduction :=
⟨ λ eqs, repr eqs.eqs ⟩

def EqsReduction.then (r: EqsReduction) (f: Eqs → EqsReduction): EqsReduction :=
	let r2 := f r.eqs in ⟨ r2.eqs, r.reduction ∘ r2.reduction ⟩

def EqsReduction.chain (r: EqsReduction) (f: Eqs → option EqsReduction): option EqsReduction :=
	(f r.eqs).bind (λ r2, some ⟨ r2.eqs, r.reduction ∘ r2.reduction ⟩)

def option.chain_red (a: option EqsReduction) (f: Eqs → option EqsReduction): option EqsReduction :=
	a.bind (λ r, r.chain f)

def divide_by_gcd' : Eqs → option Eqs
| ⟨ d, (eq::eqs) ⟩ := if (gcd_list eq.as) ∣ eq.c.nat_abs
	then (divide_by_gcd' ⟨ d, eqs ⟩).map (λ eqs', ⟨ d, ((eq.div (gcd_list eq.as))::eqs'.eqs) ⟩)
	else none
| ⟨ d, [] ⟩ := some ⟨ d, [] ⟩

def divide_by_gcd (e: Eqs) : option EqsReduction :=
	(divide_by_gcd' e).map (λ eqs, EqsReduction.mk eqs id)

def eliminate_unit_var (e: Eqs): option EqsReduction :=
	match find_isolated_var e with
	| none := none
	| some (a, b) :=
		some (
			let var_def := (e.eqs.inth a)
			in EqsReduction.mk
				((Eqs.mk e.dim ((e.eqs.remove_nth a).map (λ eq, annihilate_var eq var_def b))).remove_column b)
				(λ s, s.insert_nth b ((var_def.c - (smul (var_def.remove_column b).as s)) / (var_def.as.inth b)))
		)
	end

def remove_zero_eqs (e: Eqs): option EqsReduction := some ⟨ Eqs.mk e.dim (e.eqs.filter (λ eq, !eq.is_zero)), id ⟩

def reduce (e: Eqs): option EqsReduction :=
	match find_min_non_zero_or_default e with
	| none := none
	| some (a, b) :=
		let
			eq := e.eqs.inth a,
			ak := eq.as.inth b,
			m := ak.nat_abs + 1,
			eq' := Eq.mk (m::(eq.as.map (λ a, mod' a m))) (mod' eq.c m),
			s1 := some (
				EqsReduction.mk (e.insert_column.cons_eq eq') (λ s, s.tail)
			),
			s2 := s1.chain_red eliminate_unit_var,
			s3 := s2.chain_red divide_by_gcd
		in
			s3
	end

def coeff_sum (e: Eq): ℕ := (e.as.map (int.nat_abs)).sum

-- Simplify should decrease `t eqs`, so that `solve_eqs` terminates.
-- This is used for the termination proof.
def t (e: Eqs): /- dim -/ ℕ × /- min non-neg abs val -/ ℕ × /- coeff. abs sum in eq -/ ℕ :=
	match find_min_non_zero_or_default e with
	| none := (0, 0, 0)
	| some (a, b) := (e.dim, ((e.eqs.inth a).as.inth b).nat_abs, coeff_sum (e.eqs.inth a))
	end


def simplify (e: Eqs): option EqsReduction :=
	let
		r1 := divide_by_gcd e,
		r2 := r1.chain_red remove_zero_eqs,
		r3 := r2.chain_red (λ e1,
			match e1.eqs with
			| [] := some ⟨ Eqs.mk 0 [], λ x, list.repeat (0: ℤ) e1.dim ⟩
			| [eq] := eq.get_solution.bind (λ s, some ⟨ Eqs.mk 0 [], λ x, s ⟩)
			| _ := (eliminate_unit_var e1).orelse (reduce e1)
			end
		)
	in r3
	
meta def solve_eqs : Eqs → option (list ℤ)
| e :=
	if e.dim = 0 then some []
	else
		match simplify e with
		| none := none
		| some e1 := (solve_eqs e1.eqs).map e1.reduction
		end


def ex1 := Eqs.from [
		(Eq.mk [2, 10] (20)),
		(Eq.mk [1, 6] (4))
	]

def ex2 := Eqs.from [
		(Eq.mk [2, 0, 3, 0, -4] (10)),
		(Eq.mk [-1, 7, 0, 3, 1] (-5)),
		(Eq.mk [0, 1, 1, 0, 0] (1))
	]

def ex3 := Eqs.from [
		(Eq.mk [2, 0, 3, 1, -4] (10)),
		(Eq.mk [-1, 7, 5, 3, 2] (-5)),
		(Eq.mk [5, 3, 2, 5, 1] (1))
	]

def ex4 := Eqs.from [
		(Eq.mk [1, 2] (1)),
		(Eq.mk [2, 3] (1))
	]

def cur_eqs := ex3
meta def x := solve_eqs cur_eqs

-- This outputs a solution if one exists. Hover on the eval!
#eval x

-- This computes if x is really a solution
#eval x.map (λ s, cur_eqs.is_solution s)
