import Convex.Function.Proximal
import Convex.BCD.Subdifferential
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.NormedSpace.ProdLp
import Convex.BCD.KL

noncomputable section

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def limit_set (z : ℕ → E) :=
  {x | MapClusterPt x atTop z}

end


noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/- The gradient of the first component -/
def grad_fst (H : E × F → ℝ) (y : F) : E → E := gradient (fun t ↦ H (t, y))

/- The gradient function of the second component -/
def grad_fun_fst (H : E × F → ℝ) := fun (x, y) ↦ (grad_fst H y x)

/- The gradient of the second component -/
def grad_snd (H : E × F → ℝ) (x : E) : F → F := gradient (fun t ↦ H (x, t))

/- The gradient function of the second component -/
def grad_fun_snd (H : E × F → ℝ) := fun (x, y) ↦ (grad_snd H x y)

/- The gradient of the prod domain -/
def grad_comp (H : E × F → ℝ) (x : E) (y : F) : E × F := (grad_fst H y x, grad_snd H x y)

/- The gradient function of the prod domain -/
def grad_fun_comp (H : E × F → ℝ) := fun (x, y) ↦ (grad_comp H x y)

end

noncomputable section

open Set Bornology Filter BigOperators Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [ProperSpace F]
variable {f : E → ℝ} {g : F → ℝ} {x : E} {y : F}
variable {H : E × F → ℝ} {x0 : E} {y0 : F} {l : NNReal}
instance : ProperSpace (E × F) := inferInstance
/-
  Assumption: f and g are lower semicontinuous, H is continuously differentiable
  ∇ H is l- Lipschitz continuous, f and g are lower bounded
-/
class ProblemData (f : E → ℝ) (g : F → ℝ) (H : E × F → ℝ) (l : NNReal) : Prop where
  lbdf : BddBelow (f '' univ)
  lbdg : BddBelow (g '' univ)
  hf : LowerSemicontinuous f
  hg : LowerSemicontinuous g
  conf : ContDiff ℝ 1 H
  lpos : l > (0 : ℝ)
  lip : LipschitzWith l (grad_fun_comp H)

/-
  The definition of block coordinate descent
-/
structure BCD (f : E → ℝ) (g : F → ℝ) (H : E × F → ℝ) (l : NNReal)
    (x0 : E) (y0 : F) extends ProblemData f g H l where
  x : ℕ → E
  y : ℕ → F
  x0 : x 0 = x0
  y0 : y 0 = y0
  c : ℕ → ℝ
  d : ℕ → ℝ
  s₁ : ∀ k, prox_prop (c k • f) (x k - c k • (grad_fst H (y k) (x k))) (x (k + 1))
  s₂ : ∀ k, prox_prop (d k • g) (y k - d k • (grad_snd H (x (k + 1)) (y k))) (y (k + 1))

open BCD

/- the notation z in BCD -/
def BCD.z {self : BCD f g H l x0 y0} : ℕ → WithLp 2 (E × F) :=
  fun n ↦ (WithLp.equiv 2 (E × F)).symm (self.x n, self.y n)

/- the notation ψ in BCD -/
def BCD.ψ {_ : BCD f g H l x0 y0} := fun z : WithLp 2 (E × F) ↦ (f z.1 + g z.2 + H z)

variable {alg : BCD f g H l x0 y0} (γ : ℝ) (hγ : γ > 1)
variable (ck: ∀ (k: ℕ), alg.c k = 1 / (γ*l)) (dk: ∀ (k: ℕ), alg.d k = 1 / (γ*l))

section Assumption

def addElementToSet (A : Set E) (x : E) : Set E := {a + x | a ∈ A}

def series_sum (f : ℕ → ℝ) (n : ℕ) := (Finset.range n).sum f

lemma thm (x : E) (y : F) :‖(x,y)‖ = max ‖x‖ ‖y‖ := rfl

lemma comp_norm_le (x : E) (y : F): (‖x‖ ≤ ‖(x,y)‖)∧(‖y‖ ≤ ‖(x,y)‖) := by
  constructor
  rw [thm]
  exact le_max_left ‖x‖ ‖y‖
  rw [thm]
  exact le_max_right ‖x‖ ‖y‖

--假设条件的基本推论
--第一部分描述分量Lipschitz连续
theorem Assumption1 :
    (∀ (y : F) , LipschitzWith l (grad_fst H y)) ∧ (∀ (x : E) , LipschitzWith l (grad_snd H x)) := by
  have lip : LipschitzWith l (grad_fun_comp H) := alg.lip
  rw [lipschitzWith_iff_norm_sub_le] at lip
  constructor
  intro y
  rw [lipschitzWith_iff_norm_sub_le]
  intro x1 x2
  specialize lip (x1,y) (x2,y)
  simp [grad_fun_comp,grad_comp] at lip
  have h1:‖grad_fst H y x1 - grad_fst H y x2‖
          ≤‖(grad_fst H y x1 - grad_fst H y x2, grad_snd H x1 y - grad_snd H x2 y)‖ := by
    exact (comp_norm_le (grad_fst H y x1 - grad_fst H y x2)
                        (grad_snd H x1 y - grad_snd H x2 y)).left
  apply le_trans h1 at lip
  have :‖(x1 - x2, (0 : F))‖=‖x1 - x2‖ := by
    rw [thm]
    have :‖(0 : F)‖=0 := by exact norm_zero
    rw[this]
    apply le_antisymm
    apply max_le_iff.2
    constructor
    norm_num
    exact norm_nonneg (x1-x2)
    apply le_max_iff.2
    left
    norm_num
  rw [← this]
  exact lip
  intro x
  rw [lipschitzWith_iff_norm_sub_le]
  intro y1 y2
  specialize lip (x,y1) (x,y2)
  simp [grad_fun_comp,grad_comp] at lip
  have h2:‖grad_snd H x y1 - grad_snd H x y2‖
          ≤‖(grad_fst H y1 x - grad_fst H y2 x, grad_snd H x y1 - grad_snd H x y2)‖ := by
    exact (comp_norm_le (grad_fst H y1 x - grad_fst H y2 x)
                        (grad_snd H x y1 - grad_snd H x y2)).right
  apply le_trans h2 at lip
  have :‖((0 : E),(y1-y2))‖=‖y1 - y2‖ := by
    rw [thm]
    have :‖(0 : E)‖=0 := by exact norm_zero
    rw[this]
    apply le_antisymm
    apply max_le_iff.2
    constructor
    exact norm_nonneg (y1-y2)
    norm_num
    apply le_max_iff.2
    right
    norm_num
  rw [← this]
  exact lip
--第二部分描述次微分的拆解

theorem Assumption2 : ∀ (x : E) (y : F),
  subdifferential alg.ψ (x,y) = ( addElementToSet (subdifferential f x) (grad_fun_fst H (x,y))
                                × addElementToSet (subdifferential g y) (grad_fun_snd H (x,y)) ) := by
  sorry

end Assumption

section descent
--PALM下降量
theorem PALM_Descent
--h 连续可微 梯度h' Lₕ-Lipschitz连续
(h : E → ℝ) {h' : E → E} (Lₕ: NNReal)
(h₁ : ∀ x₁ : E, HasGradientAt h (h' x₁) x₁) (h₂ : LipschitzWith Lₕ h')
--σ 下半连续且有下界
(σ : E → ℝ) (h₃ : LowerSemicontinuous σ ) (h₄ : ∃ (M : ℝ), ∀ (x : E) , σ x ≥ M)
(t : NNReal) (h₅ : t < 1 / Lₕ):
∀ (u : E) ,∀ u₁ ∈ prox_set (fun a ↦ t * (σ a)) (u- t • (h' u)) ,
h u₁ + σ u₁ ≤ h u + σ u - 1 / 2 * (1 / t - Lₕ) * ‖u₁ - u‖^2 := by sorry

--充分下降定理
--第一部分描述函数值列的单调性
theorem Sufficient_Descent1
  (bd : Bornology.IsBounded (alg.z '' univ)) : ∀ (k :ℕ), alg.ψ (alg.z (k+1)) ≤ alg.ψ (alg.z k) := by sorry

--第二部分描述下降量
theorem Sufficient_Descent2
  (bd : Bornology.IsBounded (alg.z '' univ)) : ∃ ρ₁ > 0,
    ∀ (k : ℕ), ρ₁ / 2 * ‖alg.z (k+1) - alg.z k‖^2 ≤ alg.ψ (alg.z k) -alg.ψ (alg.z (k+1)) := by
  use (γ - 1) * l
  sorry

--第三部分描述差分点列平方可和
theorem Sufficient_Descent3
  (bd : Bornology.IsBounded (alg.z '' univ)) :∃ (M : ℝ ), Tendsto (series_sum ( fun (k : ℕ ) ↦ ‖alg.z (k+1) -alg.z k‖^2 ) ) atTop (𝓝 M) := by sorry

--第四部分描述差分点列趋于0
theorem Sufficient_Descent4
  (bd : Bornology.IsBounded (alg.z '' univ)) :∃ (M : ℝ ), Tendsto (fun (k : ℕ ) ↦ ‖alg.z (k+1) -alg.z k‖) atTop (𝓝 M) :=by sorry

end descent

section Upperbound_subd
/-
  The section of subsequences' properties.

  The key theorems here are just Lec6 p18 & p22.

  1. Prop 1 in p 19.

  - A^k_x, A^k_y ∈ ∂Ψ(x^k, y^k).

    Akx, Aky are defined as a map, and the property will be proved into seperated parts. Just Akx in it and Aky be.

    According to the proof in p19, we prove it in the following lemmas.

    1. The first equation in p19 holds.

      ∃ uᵏ ∈ ∂f, s.t. ∇ₓH(xᵏ, yᵏ) + 1⧸cᵏ (x^(k + 1) - xᵏ) + uᵏ = 0 holds.

    (p19 eq-line 1)

    Use the *prop_prox*, and *first_order_unconstrained* we can derive the partial derivative respect to x of the PALM formula to be zero.

    One should notice that, when we use *first_order_unconstrained*, we need to provide the f' of f manually.

    The last part is use the result of *first_order_unconstrained* to get the result.

    2. The vector addition in the subdifferential set closed.

    3. The euqation "A^k_x = ∇ₓ H( x k , y k ) + uᵏ" holds.

  - Upper Bound of A^k_x.

    Nearly completed, we write the docs later.


  2. Theorem in p22, we move them to a new file "IterSequenceProp.lean", need to complete.
-/

-- Define the A^k_x
def BCD.A_kx {self : BCD f g H l x0 y0} : ℕ -> E :=
  fun k => (1/(self.c k)) •
  (self.x k - self.x (k + 1)) - (grad_fst H (self.y k) (self.x k))

-- Define the A^k_y
def BCD.A_ky {self : BCD f g H l x0 y0} : ℕ -> F :=
  fun k => (1/(self.c k)) • (self.y k - self.y (k + 1)) - (grad_snd H  (self.x (k + 1)) (self.y k))

-- The lemma used in the first-order condition
-- bcd.f_k has Gradient x according to semicontinuous,
def BCD.f' {self : BCD f g H l x0 y0} (k : ℕ) : E -> E :=
  fun u => grad_fst H (self.y k) u


lemma f_hasDeriv (k : ℕ) : ∀ (x : E), HasGradientAt f ((fun x => grad_fst H (alg.y k) x) x) x := by
  sorry

def BCD.g' {self : BCD f g H l x0 y0} (k : ℕ) : F -> F :=
  fun u => grad_snd H (self.x (k + 1)) u

-- The prop form of f will induced a function fprop
def BCD.fprop {self : BCD f g H l x0 y0}(k : ℕ) : E -> ℝ :=
  (fun u ↦ (self.c k • f) u + ‖u - (self.x k - self.c k • grad_fst H (self.y k) (self.x k))‖^2 / 2)

theorem rw_fprop (k : ℕ) : alg.fprop k = (fun u ↦ (alg.c k • f) u +
  ‖u - (alg.x k - alg.c k • grad_fst H (alg.y k) (alg.x k))‖^2 / 2) := by rfl

def BCD.fprop' {self : BCD f g H l x0 y0} (k : ℕ) : E -> E :=
  (fun u ↦ (self.c k • grad_fst H (self.y k) u) + (u - (self.x k - self.c k • grad_fst H (self.y k) (self.x k))))


theorem fprop_HasGradient (k : ℕ) : ∀ (x : E), HasGradientAt (alg.fprop k) (alg.fprop' k x) x := by
  intro x
  sorry

theorem fprop_Continuous (k : ℕ) : ContinuousOn (alg.fprop' k) univ := by
  sorry

lemma fprop'_eq_zero_at_xk (k : ℕ) : (alg.fprop' k) (alg.x (k + 1)) = 0:= by
  let propx := (alg.s₁ k)
  rw[prox_prop] at propx
  rw[<-rw_fprop k] at propx
  apply first_order_unconstrained (fprop_HasGradient k)
  trivial
  apply fprop_Continuous

def BCD.gprop {self : BCD f g H l x0 y0} (k : ℕ) :=
  (fun u ↦ (self.d k • g) u + ‖u - (self.y k - self.c k • grad_snd H (self.x (k + 1)) (self.y k))‖ ^ 2 / 2)

lemma g_hasGradient_at_yk (k : ℕ) : ∀ (y : F), HasGradientAt g (alg.g' k y) y := by
  sorry

lemma g'_eq_zero_at_xk (k : ℕ) : alg.g' k y = 0 := by
  sorry

-- The prop 1 in Lec6.p18
theorem A_ks_both_are_subdiff (k : ℕ) :
  (alg.A_kx k ∈ f_subdifferential f (alg.x k)) ∧ (alg.A_ky k ∈ f_subdifferential g (alg.y k)) := by
  -- Rename some long expr
  let xk := (alg.x k)
  have h1: xk = (alg.x k) := by rfl
  rw[<-h1]

  let fn := (fun u ↦ (alg.c k • f) u + ‖u - (alg.x k - alg.c k • grad_fst H (alg.y k) (alg.x k))‖^2 / 2)
  have h_fn: fn = (fun u ↦ (alg.c k • f) u + ‖u - (alg.x k - alg.c k • grad_fst H (alg.y k) (alg.x k))‖^2 / 2) := by rfl

  let prox_x := alg.s₁ k
  rw[prox_prop] at prox_x
  rw [<-h_fn] at prox_x

  -- Formal Proof
  apply And.intro
  .
    let fn' := (fun (u : E) ↦ (grad_fst H (alg.y k) u + ((1/(alg.c k)) • (u - (alg.x k)))))
    have lem_fn': fn' = (fun (u : E) ↦ (grad_fst H (alg.y k) u + ((1/(alg.c k)) • (u - (alg.x k))))) := by rfl

    have h_fn: ∀ x : E, HasGradientAt fn (fn' x) x := by
      sorry

    have h_fnc: ContinuousOn fn' univ := by
      sorry

    have h_d_0: grad_fst H (alg.y k) (alg.x (k + 1))  + (1 / alg.c k) • ((alg.x (k + 1))  - alg.x k) = 0
    := by
      apply first_order_unconstrained h_fn prox_x h_fnc

    have h_ukx: (grad_fst H (alg.y k) (alg.x k)) ∈ f_subdifferential f xk := by
      sorry

    have h_part_x: grad_fst H (alg.y k) (alg.x (k + 1)) + (1 / alg.c k) • (alg.x (k + 1) - alg.x k) ∈ f_subdifferential f xk := by
      sorry

    have h_Akx: ∀ (k : ℕ), alg.A_kx k = grad_fst H (alg.y (k + 1)) (alg.x (k + 1)) + (1 / alg.c k) • (alg.x (k + 1) - alg.x k) - (grad_fst H (alg.y k) (alg.x k)) := by
      intro k
      rw[A_kx]

      sorry

    have rst: alg.A_kx k ∈ f_subdifferential f xk := by
      rw[A_kx]
      sorry

    sorry

  . sorry

theorem A_ky_upper_bound : ∀ k,
    ‖alg.A_ky k‖ ≤ ((1/(alg.d k)) + 1) • l • ‖alg.z k - alg.z (k + 1)‖:= by
  sorry

theorem A_ks_uppder_bound : ∀ k,
  ∃ (γ : ℝ), ‖alg.A_kx k‖ ≤ (2 • γ + 2) • l • ‖alg.z k - alg.z (k + 1)‖ := by
  sorry

theorem Ψ_subdiff_bound : ∃ ρ > 0, ∀ k, ∃ dΨ ∈ f_subdifferential alg.ψ ((alg.x (k + 1), alg.y (k + 1))),
  ‖dΨ‖ ≤ ρ * ‖alg.z (k + 1) - alg.z k‖ := by sorry

end Upperbound_subd

section limit_point
lemma limitset_property_1 (bd : Bornology.IsBounded (alg.z '' univ)) :
  (limit_set alg.z).Nonempty ∧ ( (limit_set alg.z) ⊆ critial_point alg.ψ) :=
  by sorry

lemma limitset_property_2 (bd : Bornology.IsBounded (alg.z '' univ)):
    Tendsto (fun n ↦ (EMetric.infEdist (alg.z n) (limit_set alg.z)).toReal) atTop (𝓝 0) :=
  by sorry

lemma limitset_property_3 (bd : Bornology.IsBounded (alg.z '' univ)):
    IsConnected (limit_set alg.z) ∧ IsCompact (limit_set alg.z) := by
  sorry

lemma limitset_property_4 (bd : Bornology.IsBounded (alg.z '' univ)):
    ∃(c:ℝ) , ∀ x ∈ (limit_set alg.z) , alg.ψ x = c :=by
  sorry

end limit_point

section Limited_length
theorem Limited_length (bd : Bornology.IsBounded (alg.z '' univ))
    (hψ:KL_function alg.ψ) : ∃M:ℝ , ∀ n :ℕ,∑ k in Finset.range n,‖alg.z (k+1)-alg.z k‖≤M:= by
  sorry

theorem Convergence_to_critpt (bd : Bornology.IsBounded (alg.z '' univ))
    (hψ:KL_function alg.ψ):∃z_:(WithLp 2 (E×F)),z_ ∈ (critial_point alg.ψ) ∧ Tendsto alg.z atTop (𝓝 z_):= by
  sorry

end Limited_length
end
