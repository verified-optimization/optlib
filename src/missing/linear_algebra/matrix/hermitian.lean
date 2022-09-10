import linear_algebra.matrix.hermitian
import missing.linear_algebra.matrix.nonsingular_inverse

variables {m n α : Type*} 

namespace matrix
open_locale matrix
variables [ring α] [star_ring α]

lemma is_hermitian_conj_transpose_mul_mul [fintype m] {A : matrix m m α} (B : matrix m n α)
  (hA : A.is_hermitian) : (Bᴴ ⬝ A ⬝ B).is_hermitian :=
by simp only [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose, hA.eq,
  matrix.mul_assoc]

lemma is_hermitian_mul_mul_conj_transpose [fintype m] {A : matrix m m α} (B : matrix n m α)
  (hA : A.is_hermitian) : (B ⬝ A ⬝ Bᴴ).is_hermitian :=
by simp only [is_hermitian, conj_transpose_mul, conj_transpose_conj_transpose, hA.eq,
  matrix.mul_assoc]

lemma is_hermitian_transpose_iff (A : matrix n n α) :
  Aᵀ.is_hermitian ↔ A.is_hermitian :=
⟨by { intro h, rw [← transpose_transpose A], exact is_hermitian.transpose h },
  is_hermitian.transpose⟩

lemma is_hermitian_conj_transpose_iff (A : matrix n n α) :
  Aᴴ.is_hermitian ↔ A.is_hermitian :=
⟨by { intro h, rw [← conj_transpose_conj_transpose A], exact is_hermitian.conj_transpose h },
  is_hermitian.conj_transpose⟩

@[simp] lemma is_hermitian_submatrix_equiv {A : matrix n n α} (e : m ≃ n) :
  (A.submatrix e e).is_hermitian ↔ A.is_hermitian :=
⟨λ h, by simpa using h.submatrix e.symm, λ h, h.submatrix _⟩


end matrix

namespace matrix
open_locale matrix
section comm_ring

variables [comm_ring α] [star_ring α]

lemma is_hermitian.inv [fintype m] [decidable_eq m] {A : matrix m m α}
  (hA : A.is_hermitian) : A⁻¹.is_hermitian :=
by simp [is_hermitian, conj_transpose_nonsing_inv, hA.eq]

lemma is_hermitian_inv [fintype m] [decidable_eq m] (A : matrix m m α) [invertible A]:
  (A⁻¹).is_hermitian ↔ A.is_hermitian :=
⟨λ h, by {rw [← inv_inv_of_invertible A], exact is_hermitian.inv h }, is_hermitian.inv⟩

lemma is_hermitian.adjugate [fintype m] [decidable_eq m] {A : matrix m m α}
  (hA : A.is_hermitian) : A.adjugate.is_hermitian :=
by simp [is_hermitian, adjugate_conj_transpose, hA.eq]

end comm_ring

end matrix