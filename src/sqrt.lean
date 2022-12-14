import data.real.sqrt
import tactic.linarith
import tactic.norm_num
import port_real

open real

lemma sqrt_atom.feasibility (x : ℝ) (cond : (of_nat 0) ≤ x) :
  (of_nat 0) ≤ (of_nat 1) / (of_nat 2) ∧
  sqrt x ^ 2 ≤ (of_nat 1) / (of_nat 2) * x * (of_nat 2) ∧
  (of_nat 0) ≤ x :=
by simp [of_nat] at *; simp [sq_sqrt cond, cond]; ring_nf

lemma sqrt_atom.optimality (x t : ℝ) (c2 : 0 ≤ t)
  (c1 : t ^ 2 ≤ 0.5 * x * 2 ∧ (0 : ℝ) ≤ 0.5 ∧ 0 ≤ x) :
  ∀ y, x ≤ y → t ≤ sqrt y :=
begin
  intros y hy,
  have ht2 : t ^ 2 ≤ x := by linarith [c1.1],
  have hsqrtx : sqrt x ≤ sqrt y := sqrt_le_sqrt hy,
  have ht : t ≤ sqrt x := (le_sqrt c2 c1.2.2).mpr ht2,
  exact (le_trans ht hsqrtx),
end
