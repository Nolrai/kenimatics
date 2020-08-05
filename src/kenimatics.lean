import analysis.calculus.deriv
import analysis.normed_space.real_inner_product

section -- 'vectors' implemented as arrays.
open array

-- α ^^ n is a n-dim vector of 'α's implemented as an array.
-- (not to be confused with the 'vector' type in core.init.data.vector)
notation a ` ^^ `:60 b := array b a

parameter {α : Type}
variables [nondiscrete_normed_field α] {n : ℕ}

instance : has_add (array n α) :=
  ⟨array.map₂ has_add.add⟩

@[simp]
lemma read_of_map {β} (f : α → β) (a : α ^^ n) (i)
  : (a.map f).read i = f (a.read i) := rfl

@[simp]
lemma read_of_map₂
  (f : α → α → α)
  (a b : α ^^ n) {i}
  : (map₂ f a b).read i = f (a.read i) (b.read i) := rfl

@[simp] lemma
array.add_unfold (a b : α ^^ n) (i)
  : read (a + b) i = read a i + read b i :=
  begin
  unfold has_add.add,
  simp,
  end

lemma array.add_assoc (a b c : α ^^ n) : a + b + c = a + (b + c) :=
  begin
  ext,
  unfold has_add.add,
  simp,
  apply is_associative.assoc,
  end

instance : add_semigroup (α ^^ n) :=
  { add_assoc := array.add_assoc,
  ..array.has_add }

instance : has_zero (α ^^ n) :=
  ⟨mk_array n 0⟩

@[simp] lemma read_mk_array {n} {i : fin n} {x : α}
  : (mk_array n x).read i = x := rfl

@[simp] lemma simp_zero {n} {i} : (0 : α ^^ n).read i = 0 :=
  begin
  unfold has_zero.zero,
  simp,
  end

lemma array.zero_add {n} (a : α ^^ n) : 0 + a = a :=
  begin
  ext,
  simp,
  end

lemma array.add_zero {n} (a : α ^^ n) : a + 0 = a :=
  begin
  ext,
  simp,
  end

instance : add_monoid (α ^^ n) :=
  { zero_add := array.zero_add,
    add_zero := array.add_zero,
    ..array.has_zero,
    ..array.add_semigroup
  }

instance : has_neg (α ^^ n) :=
  ⟨λ a, a.map has_neg.neg⟩

@[simp] lemma array.unfold_neg (i) (a : α ^^ n)
  : (-a).read i = - (a.read i) := rfl

instance : add_comm_group (α ^^ n) :=
  { add_left_neg := begin intro a, ext, simp, end,
    add_comm := begin intros a b, ext, simp, apply add_comm end,
    .. array.has_neg,
    .. array.add_monoid}

instance : has_scalar α (α ^^ n) :=
  ⟨λ x v, v.map (λ y, x * y)⟩

@[simp] lemma array.unfold_scalar (x : α) (a : α ^^ n) (i)
  : (x • a).read i = x * a.read i := rfl

instance : vector_space α (α ^^ n) :=
  { one_smul := begin intros a, ext, simp, end,
    mul_smul := begin intros x y a, ext, simp, apply mul_assoc end,
    smul_add := begin intros a x y, ext, simp, apply mul_add end,
    smul_zero := begin intros a, ext, simp, end,
    add_smul := begin intros a x y, ext, simp, apply add_mul, end,
    zero_smul := begin intros a, ext, simp, end,
    .. array.has_scalar
  }

lemma one_le_succ : ∀ {n : ℕ}, 1 ≤ n.succ
| 0 := refl 1
| (n +1) := nat.less_than_or_equal.step one_le_succ

@[simp] lemma foldl_simp_0 {α β} {b : β} (op : α → β → β) (a : α ^^ 0)
  : a.foldl b op = b := rfl

def array.last (a : α ^^ n.succ) := a.read ⟨n, nat.lt.base n⟩

@[simp]
lemma array.last_simp (a : α ^^ n.succ) : a.last = a.read ⟨n, nat.lt.base n⟩ := rfl

lemma foldl_simp_succ_aux {β} {b : β} (a : α ^^ n.succ) (op : α → β → β) (m)
  (h : m ≤ n)
  : d_array.iterate_aux a (λ (_x : fin n.succ), op) m (nat.le_succ_of_le h) b =
    d_array.iterate_aux a.pop_back (λ (_x : fin n), op) m h b :=
  begin
  induction m,
  {unfold d_array.iterate_aux},
  {unfold d_array.iterate_aux, simp, congr' 1, apply m_ih}
  end

@[simp]
lemma foldl_simp_succ {β} {b : β} (a : α ^^ n.succ) (op : α → β → β)
  : a.foldl b op = op a.last ((a.pop_back).foldl b op) :=
  begin
  unfold array.foldl,
  unfold array.iterate,
  unfold d_array.iterate,
  unfold d_array.iterate_aux,
  simp,
  unfold array.read,
  congr' 1,
  apply foldl_simp_succ_aux,
  end

@[simp]
lemma pop_back_simp (a : α ^^ n.succ) (i : ℕ) (i_h : i < n) : a.pop_back.read ⟨i, i_h⟩ = a.read ⟨i, nat.lt.step i_h⟩ :=
  begin
  cases a,
  unfold pop_back,
  unfold array.read,
  unfold d_array.read,
  simp,
  unfold pop_back._match_1,
  unfold array.read d_array.read,
  end

lemma foldl_induction
  {β} (P : α → Prop) (a : α ^^ n) (op : α → β → β) (b : β) (Q : β → Prop)
  : (∀ i, P (a.read i)) → Q b → (∀ x y, P x → Q y → Q (op x y))
    → Q (a.foldl b op) :=
  begin
  intros P_a Q_b P_Q_op,
  induction n,
  { rw foldl_simp_0, exact Q_b},
  { rw foldl_simp_succ,
    apply P_Q_op,
    apply P_a,
    apply n_ih,
    intros,
    cases i,
    rw pop_back_simp,
    refine P_a _
  },
  end

noncomputable
def total_deriv
  {β γ} [normed_group γ] [normed_space α γ]
  (surface : β → γ) (path : α → β) (t : α) :=
  deriv (surface ∘ path) t

def coordinate_path : fin n → (α ^^ n) → α →  α ^^ n
  | ix v₀ t := v₀.write ix (v₀.read ix + t)

end .

section real_array

parameter {n : ℕ}

instance : has_inner (ℝ ^^ n) :=
  ⟨ λ a b,
    (array.map₂ (has_mul.mul) a b).foldl
      (0 : ℝ)
      (λ x sum, x + sum)
  ⟩

@[simp]
lemma has_inner_unfold (x y : ℝ ^^ n) :
 inner x y =
  (array.map₂ (has_mul.mul) x y).foldl
    (0 : ℝ)
    (λ r sum, r + sum) := rfl

lemma congr_fun₂ {α β γ} {f f_1 : α → β → γ} (e_1 : f = f_1) (a : α) (b) :
  f a b = f_1 a b := congr_fun (congr_fun e_1 a) b

lemma map₂_comm
  (a b : ℝ ^^ n) (op : ℝ → ℝ → ℝ)
  (comm : ∀ x y : ℝ, op x y = op y x) :
  array.map₂ op a b = array.map₂ op b a :=
  array.ext
    (λ i,
      calc (array.map₂ op a b).read i
          = op (a.read i) (b.read i) : by {apply read_of_map₂}
      ... = op (b.read i) (a.read i) : comm _ _
      ... = (array.map₂ op b a).read i : (read_of_map₂ op b a).symm
    )

lemma real_array.inner_comm (x y : ℝ ^^ n) : inner x y = inner y x :=
  have e_1 : array.map₂ (*) x y = array.map₂ (*) y x,
    from map₂_comm _ _ _ mul_comm,
  have e_2 : (array.map₂ (*) x y).foldl 0 (+) = (array.map₂ (*) y x).foldl 0 (+),
    from congr_fun₂ (congr_arg array.foldl e_1) 0 (+),
  e_2 -- it doesn't work if don't seperate out its body into the above have statement.

lemma real_array.nonneg (x : ℝ ^^ n) : 0 ≤ inner x x :=
  begin
  dsimp,
  apply foldl_induction (λ r : ℝ, 0 ≤ r),
  { intros, dsimp, apply mul_self_nonneg },
  exact le_refl 0,
  {apply add_nonneg},
  end

lemma real_array.definiate (x : ℝ ^^ n) : inner x x = 0 → x = 0 :=
  begin
  contrapose,
  end

noncomputable
instance : inner_product_space.core (ℝ ^^ n) :=
  { comm := real_array.inner_comm,
    nonneg := real_array.nonneg,
    definite := _,
    add_left := _,
    smul_left := _,
    .. array.has_inner
  }