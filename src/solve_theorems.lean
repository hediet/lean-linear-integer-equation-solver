import .definitions
import data.bool
import data.int.gcd
import tactic
import .mod
import .solve
import .main

lemma divide_by_gcd'_correct (eqs eqs': Eqs)
	(h1: divide_by_gcd' eqs = some eqs')
	(x: list ℤ) (h2: x ∈ eqs):
	(x ∈ eqs') ∧ (t eqs' ≤ t eqs) :=
begin
	cases eqs,
	cases eqs',
	cases eqs_eqs;
	unfold divide_by_gcd' at h1,
	{
		rw Eqs.has_mem_iff at h2,
		simp at h2,
		simp at h1,
		rw Eqs.has_mem_iff,
		simp [t, ←h1.2],
		cases  (find_min_non_zero_or_default {dim := eqs'_dim, eqs := list.nil});
		simp [t._match_1, *],
	}, {
		sorry,
	}
end

theorem divide_by_gcd_correct (e: Eqs) (r: EqsReduction)
	(h1: divide_by_gcd e = some r)
	(x: list ℤ) (h2: x ∈ r.eqs):
	(r.reduction x ∈ e) ∧ (t r.eqs ≤ t e) :=
begin
	unfold divide_by_gcd at h1,
	sorry,
end


@[simp]
lemma Eq.add_length (eq1 eq2: Eq): (eq1.add eq2).as.length = min eq1.as.length eq2.as.length :=
by simp [Eq.add]

@[simp]
lemma Eq.mul_length (eq: Eq) (f: ℤ): (eq.mul f).as.length = eq.as.length :=
by simp [Eq.mul]

lemma annihilate_var_correct (e: Eq) (var_def: Eq) (i: ℕ) (h: (e.as.inth i).nat_abs = 1) (h': var_def.as.length = e.as.length) (x: list ℤ) (h2: x ∈ var_def):
	x ∈ (annihilate_var e var_def i) ↔ x ∈ e :=
begin
	rw Eq.has_mem_iff at h2,
	
	rw Eq.has_mem_iff,
	rw Eq.has_mem_iff,
	unfold annihilate_var,

	apply and_congr, { simp [h2, h'], },
		
	simp,
	split, {
		assume h2,
		sorry,
	},
	sorry,
end

theorem eliminate_unit_var_correct (e: Eqs) (r: EqsReduction)
	(h1: eliminate_unit_var e = some r)
	(x: list ℤ) (h2: x ∈ r.eqs):
	(r.reduction x ∈ e) ∧ (t r.eqs ≤ t e) :=
begin
	unfold eliminate_unit_var at h1,
	cases find_isolated_var e,
	{
		unfold eliminate_unit_var._match_1 at h1,
		finish,
	}, {
		cases val,
		unfold eliminate_unit_var._match_1 at h1,
		simp at h1,

		split, {
			subst h1,
			simp at h2,
			simp,
			sorry,
		},
		sorry,
	}
end

theorem fixpoint_of_simplify_terminates (eqs: Eqs) (r: EqsReduction)
	(h1: simplify eqs = some r): (t r.eqs < t eqs) :=
begin
	sorry,
end
