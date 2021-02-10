import data.bool
import data.int.gcd
import tactic

def mod' (a: ℤ) (b: ℕ): ℤ := a - b * ((a + b/2) / b)

theorem mod'_eq (a: ℤ) (b: ℕ): mod' a b = ((a + b / 2) % b - b / 2) :=
begin
	simp [mod', int.mod_def],
	linarith,
end

theorem mod_lower_bound (a: ℤ) (b: ℕ) (h: b ≠ 0): mod' a b ≥ -((b: ℤ) / 2) :=
by simp [mod'_eq, int.mod_nonneg, int.coe_nat_ne_zero, h]

theorem div_mul_gt (a: ℤ) { b: ℤ } (h: b > 0):  a / b * b > a - b := begin
	have := int.div_add_mod a b,
	have : (a / b) * b = a - a % b := by linarith,
	rw this,
	have := int.mod_lt a (ne_of_gt h),
	rw int.abs_eq_nat_abs at this,
	rw int.nat_abs_of_nonneg (le_of_lt h) at this,
	linarith,
end

theorem mod_upper_bound (a: ℤ) (b: ℕ) (h: b ≠ 0): (mod' a b) ≤ (b: ℤ) / 2 :=
begin
	set m := (a + (b: ℤ) / 2) % b with m_def,

	suffices : m ≤ (b: ℤ) / 2 + (b: ℤ) / 2, {
		rw [mod'_eq],
		linarith,
	},

	have : m ≤ (b: ℤ) - 1 := begin
		have := int.mod_lt (a + (b: ℤ) / 2) (int.coe_nat_ne_zero.mpr h),
		simp at this,
		exact int.le_sub_one_iff.mpr this,
	end,

	have c : (b: ℤ) - 1 ≤ (b: ℤ) / 2 * 2 := begin
		have : (2: ℤ) > 0 := by linarith,
		have := div_mul_gt b this,
		linarith,
	end,

	linarith,
end

theorem mod_abs_bound (a: ℤ) (b: ℕ) (h: b ≠ 0): (mod' a b).nat_abs ≤ b / 2 :=
begin
	rw ←int.coe_nat_le,
	rw ←int.abs_eq_nat_abs,
	rw abs_le,
	exact and.intro (mod_lower_bound a b h) (mod_upper_bound a b h),
end