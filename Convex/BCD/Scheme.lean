import Convex.Function.Proximal

noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/- The gradient of the first component -/
def grad_fst (H : E × F → ℝ) (y : F) : E → E := gradient (fun t ↦ H (t, y))

/- The gradient of the second component -/
def grad_snd (H : E × F → ℝ) (x : E) : F → F := gradient (fun t ↦ H (x, t))

/- The gradient of the prod domain -/
def grad_comp (H : E × F → ℝ) (x : E) (y : F): E × F := (grad_fst H y x, grad_snd H x y)

/- The gradient function of the prod domain -/
def grad_fun_comp (H : E × F → ℝ) := fun (x, y) ↦ (grad_comp H x y)

end

section BCD

open Set Bornology Filter

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g : E → ℝ} {x : E} {H : E × E → ℝ}

/-
  The definition of block coordinate descent
  Assumption: f and g are lower semicontinuous, H is continuously differentiable
  ∇ H is l- Lipschitz continuous, f and g are lower bounded
-/
class BCD (f g : E → ℝ) (H : E × E → ℝ) :=
  (x : ℕ → E) (y : ℕ → E) (z := fun n ↦ (x n, y n))
  (ψ := fun (x, y) ↦ (f x + g y + H (x, y))) (c : ℕ → ℝ) (d : ℕ → ℝ) (l : NNReal)
  (lbdf : BddBelow (f '' univ)) (lbdg : BddBelow (g '' univ))
  (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
  (conf : ContDiff ℝ 1 H) (lip : LipschitzWith l (grad_fun_comp H))
  (s₁ : ∀ k, prox_prop (c k • f) (x k - c k • (grad_fst H (y k) (x k))) (x (k + 1)))
  (s₂ : ∀ k, prox_prop (d k • g) (y k - c k • (grad_snd H (x (k + 1)) (y k))) (y (k + 1)))

end BCD
