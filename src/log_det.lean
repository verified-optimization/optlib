import missing.linear_algebra.matrix.ldl
import schur_complement
import subadditivity

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

lemma LDL.diag_entries_pos {A : matrix n n ℝ} (hA: A.pos_def) (i : n) :
  0 < LDL.diag_entries hA i :=
begin
  have : (LDL.lower_inv hA).det ≠ 0, by simp [LDL.det_lower_inv hA],
  have : LDL.lower_inv hA i ≠ 0,
    from λ h, this (matrix.det_eq_zero_of_row_eq_zero i (λ j, congr_fun h j)),
  exact hA.2 (LDL.lower_inv hA i) this,
end

lemma det_log_atom.solution_eq_atom {A : matrix n n ℝ} (hA: A.pos_def) :
  (∑ i, real.log (LDL.diag_entries hA i)) = real.log (A.det) :=
begin
  conv { to_rhs, rw [(LDL.lower_conj_diag hA).symm] },
  have := real.log_prod finset.univ (LDL.diag_entries hA)
    (λ i _, ne_of_gt (LDL.diag_entries_pos hA i)),
  simp [LDL.diag, this.symm]
end

lemma det_log_atom.feasibility_exp {A : matrix n n ℝ} (hA: A.pos_def) (i : n) :
  LDL.diag_entries hA i ≤ ((LDL.diag hA) ⬝ ((LDL.lower hA)ᵀ)).diag i :=
by simp [LDL.diag]

def to_upper_tri {m α : Type*} [linear_order m] [has_zero α] (A : matrix m m α) : matrix m m α :=
λ i j, if i ≤ j then A i j else 0

lemma is_hermitian₁₁_of_is_hermitian_to_block
  {A B C D : matrix n n ℝ} (h : (from_blocks A B C D).is_hermitian) :
  is_hermitian A :=
by { ext i j, simpa using congr_fun (congr_fun h (sum.inl i)) (sum.inl j) }

lemma is_hermitian₂₂_of_is_hermitian_to_block
  {A B C D : matrix n n ℝ} (h : (from_blocks A B C D).is_hermitian) :
  is_hermitian D :=
by { ext i j, simpa using congr_fun (congr_fun h (sum.inr i)) (sum.inr j) }

lemma pos_semidef₁₁_of_pos_semidef_to_block
  {A B C D : matrix n n ℝ}
  (h_posdef : (from_blocks A B C D).pos_semidef) :
  pos_semidef A :=
⟨is_hermitian₁₁_of_is_hermitian_to_block h_posdef.1,
  λ x, by simpa [matrix.from_blocks_mul_vec, star] using h_posdef.2 (sum.elim x 0)⟩

lemma pos_semidef₂₂_of_pos_semidef_to_block
  {A B C D : matrix n n ℝ}
  (h_posdef : (from_blocks A B C D).pos_semidef) :
  pos_semidef D :=
⟨is_hermitian₂₂_of_is_hermitian_to_block h_posdef.1,
  λ x, by simpa [matrix.from_blocks_mul_vec, star] using h_posdef.2 (sum.elim 0 x)⟩

lemma upper_triangular_to_upper_tri (A : matrix n n ℝ) : A.to_upper_tri.upper_triangular :=
begin
  intros i j hij,
  unfold to_upper_tri,
  rw [if_neg],
  simpa using hij,
end

lemma det_log_atom.optimality_D_posdef {t : n → ℝ} {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.to_upper_tri)
  (h_posdef : (from_blocks D Z Zᵀ A).pos_semidef) :
  D.pos_def :=
begin
  have h_D_psd : D.pos_semidef := pos_semidef₁₁_of_pos_semidef_to_block h_posdef,
  show D.pos_def,
  { rw [h_D_psd.pos_def_iff_det_ne_zero, hD, det_diagonal, finset.prod_ne_zero_iff],
    exact λ i _, ne_of_gt (lt_of_lt_of_le ((t i).exp_pos) (ht i)) },
end

lemma det_log_atom.optimality_Ddet_le_Adet {t : n → ℝ} {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.to_upper_tri)
  (h_posdef : (from_blocks D Z Zᵀ A).pos_semidef) :
  D.det ≤ A.det :=
begin
  by_cases h_nonempty : nonempty n,
  { have h_D_pd : D.pos_def, from det_log_atom.optimality_D_posdef ht hD hZ h_posdef,
    haveI h_D_invertible : invertible D := h_D_pd.invertible,
    have h_Zdet : Z.det = D.det,
    { rw [hZ, det_of_upper_triangular (upper_triangular_to_upper_tri Y), hD, det_diagonal],
      simp [to_upper_tri], },
    have h_ZDZ_semidef : (Zᴴ ⬝ D⁻¹ ⬝ Z).pos_semidef,
    from pos_semidef.conj_transpose_mul_mul D⁻¹ Z h_D_pd.nonsingular_inv.pos_semidef,
    have h_AZDZ_semidef : (A - Zᴴ ⬝ D⁻¹ ⬝ Z).pos_semidef,
      from (pos_semidef.from_blocks₁₁ Z A h_D_pd).1 h_posdef,
    show D.det ≤ A.det,
    { apply le_of_add_le_of_nonneg_left _ h_AZDZ_semidef.det_nonneg,
      simpa [h_Zdet] using det_add_det_le_det_add _ _ h_ZDZ_semidef h_AZDZ_semidef } },
  { haveI h_empty := not_nonempty_iff.1 h_nonempty,
    simp only [matrix.det_is_empty] }
end

lemma det_log_atom.cond_elim {t : n → ℝ} {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.to_upper_tri)
  (h_posdef : (from_blocks D Z Zᵀ A).pos_semidef) :
  A.pos_def :=
begin
  have h_D_pd : D.pos_def, from det_log_atom.optimality_D_posdef ht hD hZ h_posdef,
  have h_A_psd : A.pos_semidef := pos_semidef₂₂_of_pos_semidef_to_block h_posdef,
  have h_Ddet_le_Adet : D.det ≤ A.det := det_log_atom.optimality_Ddet_le_Adet ht hD hZ h_posdef,
  have h_Adet_pos : 0 < A.det, from lt_of_lt_of_le h_D_pd.det_pos h_Ddet_le_Adet,
  rw h_A_psd.pos_def_iff_det_ne_zero,
  apply ne_of_gt h_Adet_pos
end

lemma det_log_atom.optimality {t : n → ℝ} {Y Z D : matrix n n ℝ} (ht : ∀ i, (t i).exp ≤ Y.diag i)
  (hD : D = matrix.diagonal (Y.diag)) (hZ : Z = Y.to_upper_tri)
  (h_posdef : (from_blocks D Z Zᵀ A).pos_semidef) :
  ∑ i, t i ≤ real.log A.det :=
begin
  have h_A_pd : A.pos_def, from det_log_atom.cond_elim ht hD hZ h_posdef,
  have h_Ddet_le_Adet : D.det ≤ A.det := det_log_atom.optimality_Ddet_le_Adet ht hD hZ h_posdef,
  have h_Adet_pos: 0 < A.det, from h_A_pd.det_pos,
  rw [←real.exp_le_exp, real.exp_sum, real.exp_log h_Adet_pos],
  apply le_trans (finset.prod_le_prod (λ i _, le_of_lt ((t i).exp_pos)) (λ i _, ht i)),
  convert h_Ddet_le_Adet,
  simp [hD]
end



end matrix
