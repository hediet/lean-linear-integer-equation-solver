import .definitions
import data.bool
import data.int.gcd
import tactic

@[simp]
theorem rdiv_cons (a: ℤ) (as: list ℤ) (f: ℤ): rdiv (a :: as) f = ((a / f) :: rdiv as f) :=
by simp [rdiv]

@[simp]
theorem rdiv_length (as: list ℤ) (f: ℤ): (rdiv as f).length = as.length :=
by simp [rdiv]

@[simp]
theorem rmul_cons (a: ℤ) (as: list ℤ) (f: ℤ): rmul (a :: as) f = ((a * f) :: rmul as f) :=
by simp [rmul]

@[simp]
theorem rmul_length (as: list ℤ) (f: ℤ): (rmul as f).length = as.length :=
by simp [rmul]

@[simp]
theorem smul_cons (a b: ℤ) (as bs: list ℤ): smul (a::as) (b::bs) = a * b + smul as bs :=
by simp [smul, list.zip_cons_cons]

@[simp]
theorem smul_rmul_right (as bs: list ℤ) (f: ℤ): smul as (rmul bs f) = (smul as bs) * f := begin
	induction bs generalizing as,
	{ simp [smul, rmul], },
	{
		cases as,
		{ simp [smul], },
		simp only [bs_ih, smul_cons, rmul_cons],
		linarith,
	},
end

@[simp]
theorem smul_rmul_left (as bs: list ℤ) (f: ℤ): smul (rmul as f) bs = (smul as bs) * f := begin
	induction as generalizing bs,
	{ simp [smul, rmul], },
	{
		cases bs,
		{ simp [smul], },
		simp only [as_ih, smul_cons, rmul_cons],
		linarith,
	},
end

theorem dvd_dvd_smul_left (as bs: list ℤ) (d: ℤ) (h: ∀ a ∈ as, d ∣ a): d ∣ smul as bs :=
begin
	induction as generalizing bs,
	{ simp [smul], },
	{
		cases bs, { simp [smul], },
		{
			simp,
			have := h as_hd (list.mem_cons_self _ _),
			replace this := dvd_mul_of_dvd_left this bs_hd,
			replace as_ih := as_ih _ bs_tl,
			exact dvd_add this as_ih,

			assume a ah,
			simp [list.mem_cons_of_mem, *],
		}
	},
end


@[simp]
theorem gcd_list_gcd (a: ℤ) (as: list ℤ): gcd_list (a::as) = a.nat_abs.gcd (gcd_list as) :=
begin
	cases as,
	{ simp [gcd_list], },
	{ simp [gcd_list], },
end

theorem gcd_list_dvd (as: list ℤ) (a: ℤ) (h: a ∈ as): gcd_list as ∣ a.nat_abs :=
begin
	induction as,
	{ finish, },
	simp at h,
	cases h,
	{
		cases as_tl,
		{ simp [gcd_list, *], },
		{ simp [gcd_list, h, (int.nat_abs as_hd).gcd_dvd_left], }
	},
	{
		replace as_ih := as_ih h,
		simp,
		have := (nat.gcd_dvd (as_hd.nat_abs) (gcd_list as_tl)).2,
		exact dvd.trans this as_ih,
	}
end

@[simp]
theorem xgcd_list_length (as: list ℤ): (xgcd_list as).length = as.length :=
begin
	induction as,
	simp [xgcd_list],
	cases as_tl;
	simp [xgcd_list, *],
end

theorem xgcd_list_smul (xs: list ℤ): smul xs (xgcd_list xs) = gcd_list xs :=
begin
	induction xs,
	{ refl, },

	cases xs_tl, {
		by_cases h: xs_hd < 0,
		{
			have : xs_hd ≤ 0 := by linarith,
			simp [xgcd_list, smul, gcd_list, h, int.of_nat_nat_abs_of_nonpos this],
		},
		
		{
			have : xs_hd ≥ 0 := by linarith,
			simp [xgcd_list, smul, gcd_list, h],
			unfold_coes,
			rw int.of_nat_nat_abs_eq_of_nonneg this,
		}
	},

	by_cases c: xs_hd < 0,
	{
		have : xs_hd ≤ 0 := by linarith,
		simp [xgcd_list, smul_cons, xgcd_list, xs_ih, gcd_list, c, nat.gcd_eq_gcd_ab, int.of_nat_nat_abs_of_nonpos this],
	},
	{
		have : xs_hd ≥ 0 := by linarith,
		simp [xgcd_list, smul_cons, xgcd_list, xs_ih, gcd_list, c, nat.gcd_eq_gcd_ab],
		unfold_coes,
		rw int.of_nat_nat_abs_eq_of_nonneg this,
		simp,
	},
end


theorem Eq.has_mem_iff (eq: Eq) (xs: list ℤ) : xs ∈ eq ↔ xs.length = eq.as.length ∧ smul eq.as xs = eq.c :=
by simp [has_mem.mem, Eq.is_solution]


theorem Eq.get_solution_mem { eq: Eq } { s: list ℤ } (h: s ∈ eq.get_solution): s ∈ eq :=
begin
	unfold Eq.get_solution at h,
	cases c: eq.has_solution,
	case bool.ff { finish, },
	case bool.tt {
		simp only [c, if_true, bool.coe_sort_tt, option.mem_def] at h,
		simp only [Eq.has_solution, to_bool_iff] at c,
		replace c : ((gcd_list eq.as) : ℤ) ∣ eq.c := int.coe_nat_dvd_left.mpr c,
		cases c with f c,
		by_cases x: eq.c = 0, {
			simp [x] at h,
			simp [Eq.has_mem_iff, ←h, x],
		},
		simp [x] at h,

		have : (gcd_list eq.as : ℤ)  ≠ 0 := begin
			rw c at x,
			exact left_ne_zero_of_mul x,
		end,

		rw int.div_eq_of_eq_mul_right this c at h,
		simp [Eq.has_mem_iff, ←h, xgcd_list_smul, c],
	},
end

theorem Eq.get_solution_neq_none_iff (eq: Eq): eq.get_solution ≠ none ↔ eq.has_solution :=
begin
	unfold Eq.get_solution,
	cases eq.has_solution;
	finish,
end

theorem Eq.has_solution_iff (eq: Eq) : eq.has_solution ↔ ∃ xs, xs ∈ eq :=
begin
	split, {
		assume h,
		have := eq.get_solution_neq_none_iff.2 h,
		cases s: eq.get_solution,
		{ finish, },
		use val,
		exact Eq.get_solution_mem s,
	}, {
		assume h,
		cases h with s h,
		rw Eq.has_mem_iff at h,
		simp [Eq.has_solution],


		have := dvd_dvd_smul_left eq.as s (gcd_list eq.as) _,
		rw h.2 at this,
		exact int.coe_nat_dvd_left.mp this,

		assume a ah,
		have := gcd_list_dvd eq.as a ah,
		exact int.coe_nat_dvd_left.mpr this,
	}
end

theorem Eq.equiv_mul (eq: Eq) (f: ℤ) (f_neq_z: f ≠ 0): eq.equiv (Eq.mk (rmul eq.as f) (eq.c * f)) :=
begin
	unfold Eq.equiv,
	assume xs,
	split, {
		assume h,
		rw Eq.has_mem_iff at h,
		rw Eq.has_mem_iff,
		unfold_projs,
		simp [h],
	}, {
		assume h,
		rw Eq.has_mem_iff at h,
		rw Eq.has_mem_iff,
		unfold_projs at h,
		simp at h,
		finish,
	}
end

/-
theorem Eq.equiv_div (eq: Eq) (h: eq.has_solution): eq.equiv (Eq.mk (rdiv eq.as (gcd_list eq.as)) (eq.c / (gcd_list eq.as))) :=
begin
	unfold Eq.equiv,
	assume xs,
	split, {
		assume h,
		rw Eq.has_mem_iff at h,
		rw Eq.has_mem_iff,
		unfold_projs,
		simp [h],
		sorry,
	},
	sorry,
end
-/

theorem Eqs.has_mem_iff (e: Eqs) (xs: list ℤ) : xs ∈ e ↔ xs.length = e.dim ∧ e.eqs.all (λ eq, eq.is_solution xs) :=
by simp [has_mem.mem, Eqs.is_solution]
