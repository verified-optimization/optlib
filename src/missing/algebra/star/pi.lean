import algebra.star.pi

lemma function.star_sum_elim {I J α : Type*} (x : I → α) (y : J → α) [has_star α] :
  star (sum.elim x y) = sum.elim (star x) (star y) :=
by { ext x, cases x; simp }