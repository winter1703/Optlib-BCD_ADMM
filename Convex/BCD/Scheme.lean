import Convex.Function.Proximal

noncomputable section

open Set

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g : E → ℝ} {x : E} {H : E × E → ℝ}

local notation "∇" => gradient

def grad_comp_x (H : E × E → ℝ) (y : E) : E → E := gradient (fun t ↦ H (t, y))
def grad_comp_y (H : E × E → ℝ) (x : E) : E → E := gradient (fun t ↦ H (x, t))
def gradient_comp (H : E × E → ℝ) (x y : E) : E × E := (grad_comp_x H y x, grad_comp_y H x y)
def grad_fun_comp (H : E × E → ℝ) := fun (x, y) ↦ (gradient_comp H x y)

class BCD (f g : E → ℝ) (H : E × E → ℝ) :=
  (x : ℕ → E) (y : ℕ → E) (z := fun n ↦ (x n, y n))
  (ψ := fun (x, y) ↦ (f x + g y + H (x, y)))
  (l : NNReal) (c : ℕ → ℝ) (d : ℕ → ℝ)
  (lbdf : BddBelow (f '' univ)) (lbdg : BddBelow (g '' univ))
  (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g)
  (conf : ContDiff ℝ 1 H) (lip : LipschitzWith l (grad_fun_comp H))
  (s₁ : ∀ k, prox_prop (c k • f) (x k - c k • (grad_comp_x H (y k) (x k))) (x (k + 1)))
  (s₂ : ∀ k, prox_prop (d k • g) (y k - c k • (grad_comp_y H (x (k + 1)) (y k))) (y (k + 1)))

end
