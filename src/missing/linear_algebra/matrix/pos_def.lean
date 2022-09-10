import linear_algebra.matrix.pos_def

namespace matrix
variables {𝕜 : Type*} [is_R_or_C 𝕜] {m n : Type*} [fintype m] [fintype n]


/-- A matrix `M : matrix n n 𝕜` is positive semidefinite if it is hermitian
   and `xᴴMx` is nonnegative for all `x`. -/
def pos_semidef (M : matrix n n 𝕜) :=
M.is_hermitian ∧ ∀ x : n → 𝕜, 0 ≤ is_R_or_C.re (dot_product (star x) (M.mul_vec x))

lemma pos_def.pos_semidef {M : matrix n n 𝕜} (hM : M.pos_def) : M.pos_semidef :=
begin
  refine ⟨hM.1, _⟩,
  intros x,
  by_cases hx : x = 0,
  { simp only [hx, zero_dot_product, star_zero, is_R_or_C.zero_re'] },
  { exact le_of_lt (hM.2 x hx) }
end

lemma pos_semidef.submatrix {M : matrix n n 𝕜} (hM : M.pos_semidef) (e : m ≃ n):
  (M.submatrix e e).pos_semidef :=
begin
  refine ⟨hM.1.submatrix e, λ x, _⟩,
  have : (M.submatrix ⇑e ⇑e).mul_vec x = M.mul_vec (λ (i : n), x (e.symm i)) ∘ e,
  { ext i,
    dsimp only [(∘), mul_vec, dot_product],
    rw finset.sum_bij' (λ i _, e i) _ _ (λ i _, e.symm i);
    simp only [eq_self_iff_true, implies_true_iff, equiv.symm_apply_apply, finset.mem_univ,
      submatrix_apply, equiv.apply_symm_apply] },
  rw this,
  convert hM.2 (λ i, x (e.symm i)) using 3,
  unfold dot_product,
  rw [finset.sum_bij' (λ i _, e i) _ _ (λ i _, e.symm i)];
  simp only [eq_self_iff_true, implies_true_iff, equiv.symm_apply_apply, finset.mem_univ,
    submatrix_apply, equiv.apply_symm_apply, pi.star_apply],
end

@[simp] lemma pos_semidef_submatrix_equiv {M : matrix n n 𝕜} (e : m ≃ n) :
  (M.submatrix e e).pos_semidef ↔ M.pos_semidef :=
⟨λ h, by simpa using h.submatrix e.symm, λ h, h.submatrix _⟩

end matrix