import analysis.calculus.deriv
import real_array

section

parameters {α : Type} [nondiscrete_normed_field α]
variables {n : ℕ}

noncomputable
def total_deriv
  {β γ} [normed_group γ] [normed_space α γ]
  (surface : β → γ) (path : α → β) (t : α) :=
  deriv (surface ∘ path) t

def coordinate_path : fin n → (α ^^ n) → α →  α ^^ n
  | ix v₀ t := v₀.write ix (v₀.read ix + t)

