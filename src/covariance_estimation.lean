import missing.linear_algebra.matrix.pos_def

open real
open matrix
open_locale real
open_locale matrix
open_locale big_operators

noncomputable def matrix.quad_form {n : ℕ} (R : matrix (fin n) (fin n) ℝ) (x : fin n → ℝ) : ℝ :=
  x ⬝ᵥ R.mul_vec x

noncomputable def gaussian_pdf {n : ℕ} (R : matrix (fin n) (fin n) ℝ) (x : fin n → ℝ) : ℝ :=
  (1 / sqrt (((2 * π) ^ n) * R.det)) * exp  (- R⁻¹.quad_form x / 2)

noncomputable def covariance_matrix {N n : ℕ} (y : fin N → fin n → ℝ) : matrix (fin n) (fin n) ℝ :=
  λ i j : fin n, (∑ k : fin N, y k i * y k j) / N

lemma gaussian_pdf_pos {n : ℕ} (R : matrix (fin n) (fin n) ℝ) (y : fin n → ℝ) (h : R.pos_def):
  0 < gaussian_pdf R y :=
mul_pos (div_pos zero_lt_one
  (sqrt_pos.2 (mul_pos (pow_pos (mul_pos (by linarith) pi_pos) _) h.det_pos))) (exp_pos _)

lemma prod_gaussian_pdf_pos {N n : ℕ} (R : matrix (fin n) (fin n) ℝ) (y : fin N → fin n → ℝ)
    (h : R.pos_def):
  0 < ∏ i : fin N, gaussian_pdf R (y i) :=
finset.prod_pos (λ i hi, gaussian_pdf_pos _ _ h)

lemma log_prod_gaussianPdf {N n : ℕ} (y : fin N → fin n → ℝ) (R : matrix (fin n) (fin n) ℝ) (hR : R.pos_def) :
    (log ∏ i : fin N, gaussian_pdf R (y i))
    = ∑ i : fin N, (log 1 - (log (sqrt ((2 * π) ^ n)) + log (sqrt (det R))) + - R⁻¹.quad_form (y i) / 2) :=
begin
    have : ∀ i,
      i ∈ finset.univ → gaussian_pdf R (y i) ≠ 0 := λ i hi, ne_of_gt (gaussian_pdf_pos _ _ hR),
    have sqrt_2_pi_n_R_det_ne_zero: sqrt ((2 * π) ^ n * R.det) ≠ 0 :=
      ne_of_gt (sqrt_pos.2 (mul_pos (pow_pos (mul_pos (by simp) pi_pos) _) hR.det_pos)),
    rw [log_prod finset.univ (λ i, gaussian_pdf R (y i)) this],
    unfold gaussian_pdf,
    apply congr_arg (finset.sum finset.univ),
    ext i,
    rw [log_mul, log_div, sqrt_mul, log_mul, log_exp],
    exact ne_of_gt (sqrt_pos.2 (pow_pos (mul_pos (by simp) pi_pos) _)),
    exact ne_of_gt (sqrt_pos.2 hR.det_pos),
    exact pow_nonneg (mul_nonneg (by simp) (le_of_lt pi_pos)) _,
    by linarith,
    exact sqrt_2_pi_n_R_det_ne_zero,
    refine div_ne_zero (by simp) sqrt_2_pi_n_R_det_ne_zero,
    exact exp_ne_zero _
end

lemma sum_quad_form {n : ℕ} (R : matrix (fin n) (fin n) ℝ) {m : ℕ} (y : fin m → fin n → ℝ) :
  (∑ i, R.quad_form (y i))
  = m * (covariance_matrix y ⬝ Rᵀ).trace :=
begin
  by_cases h : m = 0,
  { subst h, simp },
  simp only [matrix.quad_form, matrix.trace, covariance_matrix, diag, mul_apply, finset.sum_mul,
    finset.sum_div],
  simp_rw [@finset.sum_comm _ (fin m), finset.mul_sum],
  apply congr_arg,
  ext i,
  unfold dot_product,
  have : (m : ℝ) ≠ 0 := by simp [h],
  simp_rw [← mul_assoc, mul_div_cancel' _ this],
  apply congr_arg,
  ext j,
  simp_rw [mul_assoc, ← finset.mul_sum],
  apply congr_arg,
  unfold matrix.mul_vec,
  unfold dot_product,
  simp_rw [mul_comm],
  congr',
  ext j,
  rw [mul_comm, matrix.transpose]
end

lemma real.inverse_eq_inv (a : ℝ) : ring.inverse a = a⁻¹ :=
by simp

lemma matrix.pos_def.is_unit_det {n : Type*} [decidable_eq n] [fintype n]
  {M : matrix n n ℝ} (hM : M.pos_def) : is_unit M.det :=
is_unit_iff_ne_zero.2 hM.det_ne_zero

lemma is_unit_det_of_pos_def_inv {n : Type*} [decidable_eq n] [fintype n]
  {M : matrix n n ℝ} (h : M⁻¹.pos_def) :
  is_unit M.det :=
begin
  apply is_unit_iff_ne_zero.2,
  have := h.is_unit_det,
  rw [det_nonsing_inv, is_unit_ring_inverse] at this,
  apply is_unit.ne_zero this,
end
