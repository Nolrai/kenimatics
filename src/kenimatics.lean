import analysis.calculus.deriv

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
  (a b : α ^^ n) (i)
  : (map₂ f a b).read i = f (a.read i) (b.read i) := rfl

@[simp] lemma
vector_add_unfold (a b : α ^^ n) (i)
  : read (a + b) i = read a i + read b i :=
  begin
  unfold has_add.add,
  simp,
  end

lemma vector_add_assoc (a b c : α ^^ n) : a + b + c = a + (b + c) :=
  begin
  ext,
  unfold has_add.add,
  simp,
  apply is_associative.assoc,
  end

instance : add_semigroup (α ^^ n) :=
  { add_assoc := vector_add_assoc,
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

noncomputable
def total_deriv
  {β γ} [normed_group γ] [normed_space α γ]
  (surface : β → γ) (path : α → β) (t : α) :=
  deriv (surface ∘ path) t

def coordinate_path : fin n → (α ^^ n) → α →  α ^^ n
  | ix v₀ t := v₀.write ix (v₀.read ix + t)

end