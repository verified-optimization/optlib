import linear_algebra.matrix.ldl
import schur_complement
import subadditivity

section gram_schmidt

variables (𝕜 : Type*) {E : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E]
variables {ι : Type*} [linear_order ι] [locally_finite_order_bot ι] [is_well_order ι (<)]

local attribute [instance] is_well_order.to_has_well_founded

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

lemma repr_gram_schmidt_diagonal {i : ι} (b : basis ι 𝕜 E) :
  b.repr (gram_schmidt 𝕜 b i) i = 1 :=
begin
  rw [gram_schmidt_def, linear_equiv.map_sub, finsupp.sub_apply, basis.repr_self,
    finsupp.single_eq_same, sub_eq_self, linear_equiv.map_sum, finsupp.coe_finset_sum,
    finset.sum_apply, finset.sum_eq_zero],
  intros j hj,
  rw finset.mem_Iio at hj,
  simp [orthogonal_projection_singleton, gram_schmidt_triangular 𝕜 hj],
end

end gram_schmidt


namespace matrix
open_locale matrix
variables {n : Type} [fintype n] [linear_order n] [locally_finite_order_bot n]
variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {A : matrix n n ℝ} (hA : A.pos_def)

noncomputable def pos_def.invertible (hA : A.pos_def) :
  invertible A :=
invertible_of_is_unit_det A (is_unit_iff_ne_zero.2 (ne_of_gt hA.det_pos))

noncomputable instance LDL.invertible_diag : invertible (LDL.diag hA) :=
begin
  rw LDL.diag_eq_lower_inv_conj,
  refine @invertible_mul _ _ _ _ (@invertible_mul _ _ _ _ _ hA.invertible) _,
end

@[simp] lemma pos_semidef_zero : matrix.pos_semidef (0 : matrix n n 𝕜) :=
by simp [pos_semidef]

lemma det_log_atom.feasibility_pos_def {D Z : matrix n n ℝ}
  (hD : D = LDL.diag hA)
  (hZ : Z = LDL.diag hA ⬝ (LDL.lower hA)ᵀ) :
  (from_blocks D Z Zᵀ A).pos_semidef :=
begin
  have h_D_eq : D = Z ⬝ A⁻¹ ⬝ Zᴴ,
    calc D = D ⬝ D⁻¹ ⬝ D : by rw [hD, matrix.mul_inv_of_invertible, matrix.one_mul]
       ... = D ⬝ (LDL.lower_inv hA ⬝ A ⬝ (LDL.lower_inv hA)ᵀ)⁻¹ ⬝ Dᵀ
        : by erw [hD, LDL.diag, diagonal_transpose, ← LDL.diag, LDL.diag_eq_lower_inv_conj]; refl
       ... = D ⬝ (LDL.lower hA)ᵀ ⬝ A⁻¹ ⬝ (D ⬝ (LDL.lower hA)ᵀ)ᵀ
        : by simp only [hD, LDL.lower, transpose_mul, transpose_transpose, transpose_nonsing_inv,
            matrix.mul_assoc, matrix.mul_inv_rev]
       ... = Z ⬝ A⁻¹ ⬝ Zᴴ
        : by rw [hZ, hD]; refl,
  haveI := hA.invertible,
  erw pos_semidef.from_blocks₂₂ _ _ hA,
  simp [h_D_eq]
end

open_locale big_operators

lemma LDL.diag_lower_inv {A : matrix n n ℝ} (hA: A.pos_def) :
  (LDL.lower_inv hA).diag = 1 :=
begin
  rw [LDL.lower_inv_eq_gram_schmidt_basis, basis.to_matrix],
  ext i,
  simp only [diag, pi.basis_fun_apply, pi.one_apply, transpose, gram_schmidt_basis],
  simp,
  have := @repr_gram_schmidt_diagonal ℝ (n → ℝ) _
    (inner_product_space.of_matrix hA.transpose) n _ _ _ i (pi.basis_fun ℝ n),
  simpa using this
end

lemma det_log_atom.solution_eq_atom {A : matrix n n ℝ} (hA: A.pos_def) :
  (∑ i, real.log (LDL.diag_entries hA i)) = real.log (A.det) :=
begin
  conv { to_rhs, rw [(LDL.lower_conj_diag hA).symm] },
  simp only [det_mul, LDL.diag, det_diagonal],
  rw [mul_comm, ←mul_assoc, ←det_mul],


end

lemma det_log_atom.feasibility_exp {A : matrix n n ℝ} (hA: A.pos_def) (i : n) :
  LDL.diag_entries hA i ≤ ((LDL.diag hA) ⬝ ((LDL.lower hA)ᵀ)).diag i :=
sorry

lemma LDL.diag_entries_pos {A : matrix n n ℝ} (hA: A.pos_def) (i : n) :
  0 < LDL.diag_entries hA i :=
sorry

def to_upper_tri {m α : Type*} [linear_order m] [has_zero α] (A : matrix m m α) : matrix m m α :=
λ i j, if i ≤ j then A i j else 0

lemma det_log_atom.optimality (t : n → ℝ) {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.to_upper_tri)
  (h_posdef : (from_blocks D Z Zᵀ A).pos_semidef) :
  ∑ i, t i ≤ real.log A.det :=
sorry

lemma det_log_atom.cond_elim (t : n → ℝ) {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.to_upper_tri)
  (h_posdef : (from_blocks D Z Zᵀ A).pos_semidef) :
  A.pos_def :=
sorry

end matrix
