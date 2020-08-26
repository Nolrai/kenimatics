import analysis.calculus.deriv
import measure_theory.interval_integral
import real_array

section

parameters {α : Type} [nondiscrete_normed_field α]
variables {n : ℕ}

noncomputable
def total_deriv
  {β γ} [normed_group γ] [normed_space α γ]
  (surface : β → γ) (path : α → β) (t : α) :=
  deriv (surface ∘ path) t

@[simp]
lemma total_deriv_simp (surface : (α ^^ n) → α) (path : α → (α ^^ n)) :
 total_deriv surface path = deriv (surface ∘ path) := funext (λ x, rfl)

def coordinate_path : fin n → (α ^^ n) → α →  α ^^ n
  | ix v₀ t := v₀.write ix (v₀.read ix + t)

@[simp]
lemma coordinate_path_simp (ix : fin n) (v₀ : α ^^ n) (t : α) :
 coordinate_path ix v₀ t = v₀.write ix (v₀.read ix + t) := rfl

noncomputable
def partial_deriv (ix : fin n) (f : (α ^^ n) → α) (pos : α ^^ n) : α :=
  total_deriv f (coordinate_path ix pos) 0

@[simp]
lemma partial_deriv_simp (ix : fin n) (f : (α ^^ n) → α) (pos : α ^^ n) :
  partial_deriv ix f pos = deriv (λ t, f (coordinate_path ix pos t)) 0 := rfl

lemma fin.zero_ne_one : (0 : fin (n + 2)) ≠ 1 :=
  begin
    unfold has_zero.zero has_one.one fin.of_nat,
    intro zero_eq_one,
    rw fin.ext_iff at zero_eq_one,
    simp at zero_eq_one,
    have HH : (n + 1).succ = n + 2, by {clear zero_eq_one, omega},
    rw HH at zero_eq_one, clear HH,
    have H : 1 % (n + 2) = 1,
    by { apply nat.mod_eq_of_lt,
       calc 1 = 0 + 1 : (zero_add 1).symm
       ... < n + 2 : add_lt_add_of_le_of_lt (zero_le n) one_lt_two,
       },
    rw H at zero_eq_one,
    clear_except zero_eq_one,
    cases zero_eq_one,
  end

example : partial_deriv 0 (λ x : α ^^ 2, x.read 0 * x.read 1) = (λ x, x.read 1) :=
  begin
    funext,
    simp,
    rw deriv_mul,
    simp,
    rw array.read_write_of_ne,
    transitivity (pos.read 1 + 0),
    { congr,
      transitivity (pos.read 0 * 0),
      { congr' 1,
        transitivity (deriv (λ y, pos.read 1) (0 : α)),
        { congr' 1},
        {apply deriv_const},
      },
      apply mul_zero,
    },
    {apply add_zero},
    {exact fin.zero_ne_one},

    { apply differentiable.differentiable_at,
      simp_rw add_comm,
      apply differentiable.add_const,
      exact differentiable_id',
    },

    { have H :
      (λ (y : α), (pos.write 0 (pos.read 0 + y)).read 1) = (λ y, pos.read 1),
      by { funext, apply array.read_write_of_ne _ _ fin.zero_ne_one},
      rw H,
      apply differentiable_const,
    }
  end

def Lagrangian (α) (n) : Type := (α ^^ (n + n)) → α

lemma Lagrangian_def (β : Type) (m : nat) : Lagrangian β m = ((β ^^ (m + m)) → β) := rfl

variables [mα : measurable_space α]

def fin.range (n) : fin n ^^ n := ⟨id⟩

instance zero_dim_array.measurable_space : measurable_space (α ^^ 0) :=
{ is_measurable := λ s, true,
  is_measurable_empty := true.intro,
  is_measurable_compl := λ _ _, true.intro,
  is_measurable_Union := λ _ _, true.intro }

def mk_measurable : measurable_space (α ^^ n) :=
  ⨆ i, measurable_space.comap (λ a : α ^^ n, a.read i) mα

end

section

variable (n : nat)

noncomputable
def action (𝕃 : Lagrangian ℝ n) (path : ℝ → (ℝ ^^ n)) (start stop : ℝ) : ℝ :=
  ∫ t in start..stop, (𝕃 (path t ⧺ deriv path t))

structure variation (a b : ℝ) {β : Type} [inner_product_space β] :=
  (app : ℝ → β)
  (differentiable : differentiable ℝ app)
  (boundry_lower : app a = 0)
  (boundry_upper : app b = 0)

def stationary (eval : (ℝ → (ℝ ^^ n)) → ℝ → ℝ → ℝ) (path : ℝ → (ℝ ^^ n)) (start stop : ℝ) := ∀ (v : variation start stop), deriv (λ ε,eval (λ r, path r + ε • (v.app r)) start stop) (0 : ℝ) = 0

def euler_lagrange
  (𝕃 : Lagrangian ℝ n)
  (path : ℝ → (ℝ ^^ n))
  (t : ℝ) : Prop :=
  let 𝕃₁ := (cast (Lagrangian_def ℝ n) 𝕃) in
  ∀ i : fin n, ∀ t : ℝ,
      partial_deriv ⟨i, nat.lt_add_left i.val n n i.is_lt⟩ 𝕃₁ (path t ⧺ deriv path t)
      - total_deriv (partial_deriv ⟨i + n, begin cases i, simp, exact i_is_lt end⟩ 𝕃₁) (λ t, path t ⧺ deriv path t) t = 0



end
