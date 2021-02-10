import .definitions
import data.bool
import data.int.gcd
import tactic
import .main

-- Theory of Single Integer Equations

-- `eq.has_solution` correctly computes if an equation has a solution
theorem has_solution_iff (eq: Eq) : eq.has_solution ↔ ∃ xs, xs ∈ eq
:= Eq.has_solution_iff eq

-- If `eq.get_solution` computes a solution `s`, s is indeed a solution.
theorem get_solution_mem { eq: Eq } { s: list ℤ } (h: s ∈ eq.get_solution): s ∈ eq
:= Eq.get_solution_mem h

-- Only if there is no solution, `eq.get_solution` returns `none`.
theorem get_solution_neq_none_iff (eq: Eq): eq.get_solution ≠ none ↔ eq.has_solution
:= Eq.get_solution_neq_none_iff eq
