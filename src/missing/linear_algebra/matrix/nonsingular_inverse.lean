import linear_algebra.matrix.nonsingular_inverse

namespace matrix
variables {m n α : Type*}
variables (A : matrix n n α) [comm_ring α] [fintype m] [fintype n] [decidable_eq n]

instance [invertible A] : invertible A⁻¹ :=
by { rw ← inv_of_eq_nonsing_inv, apply_instance }

@[simp] lemma inv_inv_of_invertible [invertible A] : A⁻¹⁻¹ = A :=
by simp only [← inv_of_eq_nonsing_inv, inv_of_inv_of]

end matrix