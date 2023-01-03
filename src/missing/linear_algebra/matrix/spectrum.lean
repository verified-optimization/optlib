import linear_algebra.matrix.spectrum
import missing.analysis.inner_product_space.spectrum

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜] {n : Type*} [fintype n] [decidable_eq n]
variables {A : matrix n n 𝕜}

open_locale matrix
open_locale big_operators

lemma is_hermitian.has_eigenvector_eigenvector_basis (hA : A.is_hermitian) (i : n) :
  module.End.has_eigenvector A.to_lin' (hA.eigenvalues i) (hA.eigenvector_basis i) :=
begin
  simp only [is_hermitian.eigenvector_basis, orthonormal_basis.coe_reindex],
  apply linear_map.is_symmetric.has_eigenvector_eigenvector_basis
end

-- TODO: can be used to prove `spectral_theorem`.
/-- *Diagonalization theorem*, *spectral theorem* for matrices; A hermitian matrix can be
diagonalized by a change of basis using a matrix consisting of eigenvectors. -/
theorem spectral_theorem (xs : orthonormal_basis n 𝕜 (euclidean_space 𝕜 n)) (as : n → ℝ)
    (hxs : ∀ j, module.End.has_eigenvector A.to_lin' (as j) (xs j)) :
  xs.to_basis.to_matrix (pi.basis_fun 𝕜 n) ⬝ A =
    diagonal (coe ∘ as) ⬝ xs.to_basis.to_matrix (pi.basis_fun 𝕜 n) :=
begin
  rw [basis_to_matrix_basis_fun_mul],
  ext i j,
  let xs' := xs.reindex (fintype.equiv_of_card_eq (fintype.card_fin _)).symm,
  let as' : fin (fintype.card n) → ℝ := λ i, as $ (fintype.equiv_of_card_eq (fintype.card_fin _)) i,
  have hxs' : ∀ j, module.End.has_eigenvector A.to_lin' (as' j) (xs' j),
    by simp only [hxs, orthonormal_basis.coe_reindex, equiv.symm_symm, implies_true_iff],
  convert @linear_map.spectral_theorem' 𝕜 _ _
    (pi_Lp 2 (λ (_ : n), 𝕜)) _ _ (fintype.card n) A.to_lin'
    (euclidean_space.single j 1)
    ((fintype.equiv_of_card_eq (fintype.card_fin _)).symm i)
    xs' as' hxs',
  { rw [to_lin'_apply],
    simp only [orthonormal_basis.coe_to_basis_repr_apply, of_apply, orthonormal_basis.reindex_repr],
    erw [equiv.symm_apply_apply, euclidean_space.single, pi_Lp.equiv_symm_apply (2 : ennreal),
      mul_vec_single],
    simp_rw [mul_one],
    refl, },
  { simp only [diagonal_mul, (∘), as'],
    erw [basis.to_matrix_apply,
      orthonormal_basis.coe_to_basis_repr_apply, orthonormal_basis.reindex_repr,
      pi.basis_fun_apply, linear_map.coe_std_basis,
      euclidean_space.single, pi_Lp.equiv_symm_apply (2 : ennreal), equiv.symm_apply_apply,
      equiv.apply_symm_apply],
    refl, }
end

-- TODO: use this to derive `is_hermitian.det_eq_prod_eigenvalues`
/-- The determinant of a matrix is the product of its eigenvalues. -/
lemma det_eq_prod_eigenvalues (xs : orthonormal_basis n 𝕜 (euclidean_space 𝕜 n)) (as : n → ℝ)
    (hxs : ∀ j, module.End.has_eigenvector A.to_lin' (as j) (xs j)) :
  det A = ∏ i, as i :=
begin
  apply mul_left_cancel₀ (det_ne_zero_of_left_inverse
    (basis.to_matrix_mul_to_matrix_flip (pi.basis_fun 𝕜 n) xs.to_basis)),
  rw [←det_mul, spectral_theorem xs as hxs, det_mul, mul_comm, det_diagonal]
end

end matrix
