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

@[simp]
lemma has_scalar_simp (r : α) (v : α ^^ n) :
  r • v = v.map (λ y, r * y) :=
  begin
    unfold has_scalar.smul,
  end

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
end

section

parameter {α : Type}
variable {n : ℕ}
open array

lemma one_le_succ : ∀ {n : ℕ}, 1 ≤ n.succ
| 0 := refl 1
| (n +1) := nat.less_than_or_equal.step one_le_succ

@[simp] lemma foldl_simp_0 {α β} (b : β) (op : α → β → β) (a : α ^^ 0)
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

lemma fin_n_lift_fin_n_succ (i : ℕ) {p : i < n} {p' : i < n.succ} :
  (⟨i, p'⟩ : fin n.succ) = ↑(⟨i, p⟩ : fin n) :=
  begin
    rw fin.eq_iff_veq,
    simp,
    symmetry,
    exact fin.coe_val_of_lt p',
  end

@[simp]
lemma pop_back_simp' (a : α ^^ n.succ) (i : fin n) : a.pop_back.read i = a.read i :=
  begin
  cases a, cases i,
  unfold pop_back,
  unfold array.read,
  unfold d_array.read,
  simp,
  unfold pop_back._match_1,
  unfold array.read d_array.read,
  simp,
  congr,
  apply fin_n_lift_fin_n_succ,
  end

@[simp]
lemma array.map_pop_back (a : α ^^ n.succ) (f : α → α) :
  (a.map f).pop_back = a.pop_back.map f :=
  begin
  ext,
  simp,
  unfold map d_array.map d_array.foreach d_array.iterate array.read d_array.read,
  have H : ∀ {m} (x : α ^^ m) ix, x.data ix = x.read ix,
    by {clear_except, intros, unfold array.read d_array.read},
  simp_rw H,
  simp,
  end

@[simp]
lemma array.smul_pop_back [nondiscrete_normed_field α] (r : α) (a : α ^^ n +1)  :
  (r • a).pop_back = r • a.pop_back :=
  array.map_pop_back a (λ (y : α), r * y)

lemma from_pop_back (P : α → Prop) (a : α ^^ n.succ)
  (last_hyp : P (a.read ⟨n, nat.lt.base n⟩))
  (pop_back_hyp : ∀ i, P (a.pop_back.read i))
  (i : fin n.succ) : P (a.read i) :=
  begin
  obtain ⟨i, i_lt⟩ := i,
  have H : i < n ∨ i = n, from nat.lt_succ_iff_lt_or_eq.mp i_lt,
  cases H,
  { rw ← pop_back_simp, apply pop_back_hyp ⟨i,H⟩ },
  { have i_eq_n : (⟨i, i_lt⟩ : fin _) = ⟨n, _⟩,
    from ((_ : fin _).ext_iff ⟨n, nat.lt.base n⟩).mpr H,
    rw i_eq_n,
    exact last_hyp,
  }
  end

lemma foldl_induction_up
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

lemma foldl_induction_down
  {β : Type} (P : α → Prop) (a : α ^^ n) (op : α → β → β) (b : β) (Q : β → Prop)
  : (∀ x y, Q (op x y) → P x) → (∀ x y, Q (op x y) → Q y) → (Q (a.foldl b op))
    → (Q b ∧ ∀ i, P (a.read i)) :=
  begin
  intros Q_op_P Q_op_Q Q_foldl,
  induction n,

  { split,
    {rw ← foldl_simp_0 b op a, exact Q_foldl},
    {intros, apply fin.elim0 i},
  },

  { have H : Q b ∧ ∀ (i : fin n_n), P (a.pop_back.read i),
    { apply n_ih, simp at Q_foldl, refine Q_op_Q _ _ Q_foldl},
    obtain ⟨Q_b, H⟩ := H,
    split, {exact Q_b},
    { apply from_pop_back,
      rw foldl_simp_succ at Q_foldl,
      rw ← array.last_simp,
      refine Q_op_P _ _ Q_foldl,
      exact H,
    },
  },
  end

@[simp]
lemma array.map₂_pop_back (a b : α ^^ n.succ) (f : α → α → α) :
  (array.map₂ f a b).pop_back = array.map₂ f (a.pop_back) (b.pop_back) :=
  begin
  ext,
  simp,
  end

def fin.lower {m n} (i : fin (n + m)) (p : i.val >= n) : fin m :=
  ⟨i - n, (nat.sub_lt_left_iff_lt_add p).mpr i.is_lt⟩


def array.append {α n} (a : α ^^ n) {m : nat} (b : α ^^ m) :
  α ^^ (n + m) :=
    { data :=
      λ (i : fin (n+m)),
        if p: i.val < n
          then a.read ⟨i.val, p⟩
          else b.read (i.lower (not_lt.mp p))
    }

infix `⧺`:40 := (λ {α} {n m} a b, @array.append α n a m b)

end

section real_array

parameter {n : ℕ}

instance : has_inner (ℝ ^^ n) :=
  ⟨ λ a b,
    (array.map₂ (has_mul.mul) a b).foldl
      (0 : ℝ)
      (+)
  ⟩

@[simp]
lemma has_inner_unfold (x y : ℝ ^^ n) :
 inner x y =
  (array.map₂ (has_mul.mul) x y).foldl
    (0 : ℝ)
    (+) := rfl

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
  apply foldl_induction_up (λ r : ℝ, 0 ≤ r),
  { intros, dsimp, apply mul_self_nonneg },
  exact le_refl 0,
  {apply add_nonneg},
  end

def sq (x : real) : nnreal := ⟨x * x, by {exact mul_self_nonneg x}⟩

lemma nnreal.zero_sum  (x y : nnreal) : 0 = x + y → x = 0 :=
  begin
  cases x, cases y,
  unfold1 has_add.add,
  unfold1 has_zero.zero,
  simp,
  intros hyp,
  apply le_antisymm,
  { have h : x_val = 0 - y_val, by {rw hyp, ring},
    rw h, simp, exact y_property
  },
  exact x_property,
  end

lemma summ_nn (a : ℝ ^^ n) (all_nn : ∀ i, 0 ≤ a.read i)
  : 0 ≤ a.foldl (0 : ℝ) ((+) : ℝ → ℝ → ℝ) :=
  foldl_induction_up (λ (x : ℝ), 0 ≤ x) a has_add.add 0 (λ (x : ℝ), 0 ≤ x) all_nn (le_refl 0) (@add_nonneg ℝ _)

@[simp]
lemma nnreal.add_simp (x y : nnreal) : x + y = ⟨x.1 + y.1, add_nonneg x.2 y.2⟩ := rfl

lemma sum_nnreal_eq_sum_real (nna : nnreal ^^ n) (a : ℝ ^^ n)
  (all_nn : ∀ i, 0 ≤ a.read i)
  (all_eq : ∀ i, coe (nna.read i) = a.read i)
  : nna.foldl 0 (+) = ⟨a.foldl 0 (+), by {apply summ_nn a; try {assumption} }⟩ :=
  begin
    induction n,

    { simp,
      clear_except,
      apply subtype.tag_irrelevant,
    },

    { simp,
      congr,
      refine all_eq _,
      have H : nna.pop_back.foldl 0 has_add.add = ⟨a.pop_back.foldl 0 has_add.add, _⟩,
        { apply n_ih; simp; intro i,
          { apply all_nn},
          { apply all_eq},
        },
      rw H,
      simp,
    }
  end

lemma real_array.definiate (a : ℝ ^^ n) : inner a a = 0 → a = 0 :=
  begin
  intros hyp,

  have H : (0 : nnreal) = 0 ∧ ∀ i, (a.map sq).read i = 0,
  apply
    foldl_induction_down (=(0: nnreal)) (a.map sq) ((+) : nnreal → nnreal → nnreal),
  exact nnreal.zero_sum,
  exact
    λ (x y : nnreal) (hyp : 0 = x + y),
    (y.zero_sum x (hyp.trans (add_comm x y))).symm,
  { symmetry,
    transitivity (⟨(inner a a), _⟩ : nnreal),
    { simp,
      apply sum_nnreal_eq_sum_real,
      simp, intro, clear_except, exact mul_self_nonneg (array.read a i),
      simp, intro, unfold sq, simp,
    },
    {unfold1 has_zero.zero, congr, exact hyp},
  },
  obtain ⟨_, H⟩ := H, clear hyp H_left,
  ext,
  simp,
  rw ← (or_self (a.read i = 0)),
  rw ← mul_eq_zero,
  transitivity ((a.map sq).read i).val,
  { simp, unfold sq, simp},
  { rw H, simp}
  end

lemma real_array.inner_add_left (x y z : ℝ ^^ n)
  : inner (x + y) z = inner x z + inner y z :=
  begin
    induction n, {simp},
    simp at *,
    transitivity
      (x.read ⟨n_n, _⟩ * z.read ⟨n_n, _⟩ + (y.read ⟨n_n, _⟩ * z.read ⟨n_n, _⟩) +
      ( (array.map₂ has_mul.mul x z).pop_back.foldl 0 has_add.add +
        (array.map₂ has_mul.mul y z).pop_back.foldl 0 has_add.add)),

    all_goals {try {apply nat.lt.base}},

    { congr' 1,
      {apply right_distrib},
      {rw array.map₂_pop_back, unfold1 has_add.add at *, simp, apply n_ih}
    },

    { simp, ring },
  end

lemma real_array.inner_smul_left (x y : ℝ ^^ n) (r : ℝ)
  : inner (r • x) y = r * inner x y :=
  begin
    induction n,
    case nat.zero: {simp},
    case nat.succ:
      { simp at *,
        rw left_distrib,
        congr' 1,
        {apply mul_assoc},
        apply n_ih,
      },
  end

noncomputable
instance : inner_product_space.core (ℝ ^^ n) :=
  { comm := real_array.inner_comm,
    nonneg := real_array.nonneg,
    definite := real_array.definiate,
    add_left := real_array.inner_add_left,
    smul_left := real_array.inner_smul_left,
    .. array.has_inner
  }

noncomputable
instance : inner_product_space (ℝ ^^ n) :=
  begin refine inner_product_space.of_core _, apply_instance end

end real_array