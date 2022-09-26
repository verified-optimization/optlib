import missing.linear_algebra.matrix.pos_def
import missing.linear_algebra.matrix.spectrum
import missing.linear_algebra.eigenspace
import linear_algebra.matrix.ldl
import linear_algebra.matrix.dot_product


namespace finset
open_locale big_operators

lemma one_add_prod_le_prod_one_add {n : Type*} [fintype n] [nonempty n]
  (f : n → ℝ) (hf : ∀ i, 0 ≤ f i) :
  1 + (∏ i, f i) ≤ ∏ i, (1 + f i) :=
begin
classical,
calc
  1 + (∏ i, f i) =
      (∏ (a : n), 1 : ℝ) * ∏ (a : n) in univ \ univ, f a
       + (∏ (a : n) in ∅, 1) * ∏ (a : n) in univ \ ∅, f a : by simp
  ... ≤ ∑ (t : finset n),
          (∏ (a : n) in t, 1 : ℝ) * ∏ (a : n) in univ \ t, f a :
  begin
    convert finset.sum_le_univ_sum_of_nonneg _,
    { rw finset.sum_pair ,
      exact finset.univ_nonempty.ne_empty },
    { simp [hf, prod_nonneg] }
  end
  ... = ∏ i, (1 + f i) : by rw [prod_add, powerset_univ]
end

end finset

namespace matrix
variables {n : Type*} [fintype n] [decidable_eq n] [linear_order n] [locally_finite_order_bot n]
open_locale big_operators
open_locale matrix

namespace is_hermitian

variables {𝕜 : Type*} [decidable_eq 𝕜 ] [is_R_or_C 𝕜] {A : matrix n n 𝕜} (hA : A.is_hermitian)

lemma eigenvector_matrix_inv_mul :
  hA.eigenvector_matrix_inv ⬝ hA.eigenvector_matrix = 1 :=
by apply basis.to_matrix_mul_to_matrix_flip

theorem spectral_theorem' :
  hA.eigenvector_matrix ⬝ diagonal (coe ∘ hA.eigenvalues) ⬝ hA.eigenvector_matrixᴴ = A :=
by rw [conj_transpose_eigenvector_matrix, matrix.mul_assoc, ← spectral_theorem, ← matrix.mul_assoc,
    eigenvector_matrix_mul_inv, matrix.one_mul]

end is_hermitian

noncomputable def is_hermitian.sqrt {A : matrix n n ℝ} (hA : A.is_hermitian) : matrix n n ℝ :=
hA.eigenvector_matrix ⬝ matrix.diagonal (λ i, (hA.eigenvalues i).sqrt) ⬝ hA.eigenvector_matrixᵀ

lemma conj_transpose_eq_transpose {m n : Type*} {A : matrix m n ℝ} : Aᴴ = Aᵀ := rfl

@[simp] lemma pos_semidef.sqrt_mul_sqrt {A : matrix n n ℝ} (hA : A.pos_semidef) :
  hA.1.sqrt ⬝ hA.1.sqrt = A :=
calc
  hA.1.sqrt ⬝ hA.1.sqrt =
    hA.1.eigenvector_matrix ⬝ (matrix.diagonal (λ i, (hA.1.eigenvalues i).sqrt)
    ⬝ (hA.1.eigenvector_matrixᵀ ⬝ hA.1.eigenvector_matrix)
    ⬝ matrix.diagonal (λ i, (hA.1.eigenvalues i).sqrt)) ⬝ hA.1.eigenvector_matrixᵀ :
by simp [is_hermitian.sqrt, matrix.mul_assoc]
  ... = A :
begin
  rw [←conj_transpose_eq_transpose, hA.1.conj_transpose_eigenvector_matrix,
    hA.1.eigenvector_matrix_inv_mul, matrix.mul_one, diagonal_mul_diagonal,
    ← hA.1.conj_transpose_eigenvector_matrix],
  convert hA.1.spectral_theorem',
  funext i,
  rw [←real.sqrt_mul (hA.eigenvalues_nonneg i), real.sqrt_mul_self (hA.eigenvalues_nonneg i)],
  refl
end

lemma pos_semidef.pos_semidef_sqrt {A : matrix n n ℝ} (hA : A.pos_semidef) :
  hA.1.sqrt.pos_semidef :=
pos_semidef.conj_transpose_mul_mul _ _
  (pos_semidef_diagonal (λ i, real.sqrt_nonneg (hA.1.eigenvalues i)))

lemma is_hermitian.one_add {A : matrix n n ℝ} (hA : A.is_hermitian) : (1 + A).is_hermitian :=
by simp [is_hermitian, hA.eq]

lemma is_hermitian.has_eigenvector_one_add {A : matrix n n ℝ} (hA : A.is_hermitian) (i : n) :
  module.End.has_eigenvector (1 + A.to_lin') (1 + (hA.eigenvalues i)) ((hA.eigenvector_basis) i) :=
module.End.has_eigenvector_add
  (module.End.has_eigenvector_one (hA.has_eigenvector_eigenvector_basis i).2)
  (hA.has_eigenvector_eigenvector_basis i)

lemma pos_def.pos_def_sqrt {A : matrix n n ℝ} (hA : A.pos_def) :
  hA.1.sqrt.pos_def :=
begin
  unfold is_hermitian.sqrt,
  refine
    pos_def.conj_transpose_mul_mul _ (hA.1.eigenvector_matrixᵀ)
      (pos_def_diagonal (λ i, real.sqrt_pos.2 (hA.eigenvalues_pos i))) _,
  show det hA.1.eigenvector_matrixᵀ ≠ 0,
  rw [det_transpose],
  apply det_ne_zero_of_right_inverse hA.1.eigenvector_matrix_mul_inv,
end

lemma pos_semidef.pos_def_iff_det_ne_zero [decidable_eq n] {M : matrix n n ℝ} (hM : M.pos_semidef) :
  M.pos_def ↔ M.det ≠ 0 :=
begin
  refine ⟨pos_def.det_ne_zero, λ hdet, ⟨hM.1, _⟩⟩,
  intros x hx,
  apply lt_of_le_of_ne' (hM.2 x),
  rw [←hM.sqrt_mul_sqrt, ←mul_vec_mul_vec, dot_product_mul_vec, ←transpose_transpose hM.1.sqrt,
    vec_mul_transpose, transpose_transpose, ← conj_transpose_eq_transpose,
    hM.pos_semidef_sqrt.1.eq],
  simp only [is_R_or_C.re_to_real, star, id],
  change @inner ℝ (euclidean_space ℝ _) _ (hM.1.sqrt.mul_vec x) (hM.1.sqrt.mul_vec x) ≠ 0,
  intro hinner,
  have sqrtMdet0 : hM.1.sqrt.det = 0,
    from exists_mul_vec_eq_zero_iff.1 ⟨x, hx, inner_self_eq_zero.1 hinner⟩,
  rw [←hM.sqrt_mul_sqrt, det_mul, sqrtMdet0, mul_zero] at hdet,
  apply hdet rfl
end

lemma det_add_det_le_det_add' [nonempty n] (A B : matrix n n ℝ)
    (hA : A.pos_def) (hB : B.pos_semidef) :
  A.det + B.det ≤ (A + B).det :=
begin
  let sqrtA := hA.1.sqrt,
  have is_unit_det_sqrtA, from is_unit_iff_ne_zero.2 hA.pos_def_sqrt.det_ne_zero,
  have : is_unit sqrtA, from (is_unit_iff_is_unit_det _).2 is_unit_det_sqrtA,
  have is_hermitian_sqrtA : sqrtA⁻¹.is_hermitian,
  { apply is_hermitian.nonsingular_inv (hA.pos_semidef.pos_semidef_sqrt.1),
    exact is_unit_det_sqrtA },
  have pos_semidef_ABA : (sqrtA⁻¹ ⬝ B ⬝ sqrtA⁻¹).pos_semidef,
    from pos_semidef.mul_mul_of_is_hermitian hB is_hermitian_sqrtA,
  let μ := pos_semidef_ABA.1.eigenvalues,
  calc
    A.det + B.det = A.det * (1 + (sqrtA⁻¹ ⬝ B ⬝ sqrtA⁻¹).det) :
      begin
        rw [det_mul, det_mul, mul_comm _ B.det, mul_assoc, ←det_mul, ←matrix.mul_inv_rev,
          hA.pos_semidef.sqrt_mul_sqrt, mul_add, mul_one, mul_comm, mul_assoc, ←det_mul,
          nonsing_inv_mul _ (is_unit_iff_ne_zero.2 hA.det_ne_zero), det_one, mul_one]
      end
    ... = A.det * (1 + ∏ i, μ i) :
      begin
        rw pos_semidef_ABA.1.det_eq_prod_eigenvalues,
        refl
      end
    ... ≤ A.det * ∏ i, (1 + μ i) :
      begin
        apply (mul_le_mul_left hA.det_pos).2,
        apply finset.one_add_prod_le_prod_one_add μ pos_semidef_ABA.eigenvalues_nonneg
      end
    ... = A.det * (1 + sqrtA⁻¹ ⬝ B ⬝ sqrtA⁻¹).det :
      begin
        congr',
        refine (det_eq_prod_eigenvalues pos_semidef_ABA.1.eigenvector_basis
          (λ i, 1 + (pos_semidef_ABA.1.eigenvalues i)) _).symm,
        intro i,
        convert pos_semidef_ABA.1.has_eigenvector_one_add i,
        simp only [map_add, to_lin'_one, to_lin'_mul, add_left_inj],
        refl,
      end
    ... = (A+B).det :
      begin
        rw [← det_mul, ← det_conj this (A + B)],
        apply congr_arg,
        rw ←hA.pos_semidef.sqrt_mul_sqrt,
        change sqrtA ⬝ sqrtA ⬝ (1 + sqrtA⁻¹ ⬝ B ⬝ sqrtA⁻¹) = sqrtA ⬝ (sqrtA ⬝ sqrtA + B) ⬝ sqrtA⁻¹,
        rw [matrix.mul_add, matrix.mul_one, matrix.mul_add, matrix.add_mul,
          matrix.mul_assoc, matrix.mul_assoc, matrix.mul_assoc, matrix.mul_assoc,
          ← matrix.mul_assoc _ _ (B ⬝ _),
          matrix.mul_nonsing_inv _ is_unit_det_sqrtA, matrix.one_mul, matrix.mul_one,
          hA.pos_semidef.sqrt_mul_sqrt, matrix.mul_assoc]
      end
end

lemma det_add_det_le_det_add [nonempty n] (A B : matrix n n ℝ)
    (hA : A.pos_semidef) (hB : B.pos_semidef) :
  A.det + B.det ≤ (A + B).det :=
begin
  by_cases hA' : A.det = 0,
  { by_cases hB' : B.det = 0,
    { simp [hA', hB'],
      have : (A+B).pos_semidef,
      sorry,
      sorry, },
    { rw [add_comm A B, add_comm A.det B.det],
      apply det_add_det_le_det_add' _ _ (hB.pos_def_iff_det_ne_zero.2 hB') hA }, },
  { apply det_add_det_le_det_add' _ _ (hA.pos_def_iff_det_ne_zero.2 hA') hB },
end

end matrix
