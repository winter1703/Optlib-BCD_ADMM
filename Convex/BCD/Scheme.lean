import Convex.Function.Proximal
import Convex.BCD.Subdifferential
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.NormedSpace.ProdLp
import Mathlib.Topology.MetricSpace.Sequences
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
variable (ck: ∀ k, alg.c k = 1 / (γ * l)) (dk: ∀ k, alg.d k = 1 / (γ * l))

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

/- coordinate Lipschitz continuous -/
theorem ass_coordinate_lip :
    (∀ y, LipschitzWith l (grad_fst H y)) ∧ (∀ x, LipschitzWith l (grad_snd H x)) := by
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
  have : ‖(x1 - x2, (0 : F))‖ = ‖x1 - x2‖ := by
    rw [thm]
    have : ‖(0 : F)‖ = 0 := by exact norm_zero
    rw [this]; apply le_antisymm
    apply max_le_iff.2
    constructor; norm_num
    exact norm_nonneg (x1-x2)
    apply le_max_iff.2
    left; norm_num
  rw [← this]
  exact lip
  intro x
  rw [lipschitzWith_iff_norm_sub_le]
  intro y1 y2
  specialize lip (x, y1) (x, y2)
  simp [grad_fun_comp,grad_comp] at lip
  have h2:‖grad_snd H x y1 - grad_snd H x y2‖
          ≤‖(grad_fst H y1 x - grad_fst H y2 x, grad_snd H x y1 - grad_snd H x y2)‖ := by
    exact (comp_norm_le (grad_fst H y1 x - grad_fst H y2 x)
                        (grad_snd H x y1 - grad_snd H x y2)).right
  apply le_trans h2 at lip
  have : ‖((0 : E),(y1-y2))‖ = ‖y1 - y2‖ := by
    rw [thm]
    have :‖(0 : E)‖ = 0 := by exact norm_zero
    rw[this]; apply le_antisymm
    apply max_le_iff.2
    constructor; exact norm_nonneg (y1-y2)
    norm_num
    apply le_max_iff.2
    right; norm_num
  rw [← this]
  exact lip

/- the composition of the subdifferential -/
theorem ass_comp_subdiff : ∀ (x : E) (y : F),
  subdifferential alg.ψ (x,y) = (addElementToSet (subdifferential f x) (grad_fun_fst H (x,y))
                                × addElementToSet (subdifferential g y) (grad_fun_snd H (x,y))) := by
  sorry

end Assumption

section descent

/- PALM descent -/
theorem PALM_Descent (h : E → ℝ) {h' : E → E} (Lₕ: NNReal)
    (h₁ : ∀ x₁ : E, HasGradientAt h (h' x₁) x₁) (h₂ : LipschitzWith Lₕ h')
    (σ : E → ℝ) (t : ℝ) (h₅ : 0 < t) :
    ∀ (u : E), ∀ u₁ ∈ prox_set (fun a ↦ t * (σ a)) (u - t • (h' u)),
    h u₁ + σ u₁ ≤ h u + σ u - 1 / 2 * (1 / t - Lₕ) * ‖u₁ - u‖^2 := by
  have htne0 : t ≠ 0 :=  (ne_of_gt h₅)
  intro u u₁ u₁prox
  simp only [prox_set,prox_prop,isMinOn_iff] at u₁prox
  have ht : ∀ x ∈ univ, t * (σ u₁) + ‖u₁ - (u - t • (h' u))‖ ^ 2 / 2
      ≤ t * (σ x) + ‖x - (u - t • (h' u))‖ ^ 2 / 2 := u₁prox
  specialize ht u _
  exact Set.mem_univ u
  have :u - (u - t • h' u) = t • h' u := by abel
  rw [this] at ht
  have :u₁ - (u - t • h' u) = (u₁ - u) + t • h' u := by abel
  rw [this] at ht
  simp [norm_add_sq_real,this] at ht
  have h₈ :  t * σ u₁ + ‖u₁ - u‖ ^ 2 / 2 +  ⟪u₁ - u, t • h' u⟫_ℝ ≤ t * σ u := by
    linarith [ht]
  have : ⟪u₁ - u, t • h' u⟫_ℝ =t * ⟪u₁ - u, h' u⟫_ℝ := by apply inner_smul_right
  rw [this] at h₈
  have : t * (‖u₁ - u‖ ^ 2 / (2 * t)) = ‖u₁ - u‖ ^ 2 / 2 := by
    calc
      _ = (‖u₁ - u‖ ^ 2) * (t / (2 * t)) := by ring
      _ = (‖u₁ - u‖ ^ 2) * (1 / 2) := by
        simp; left
        apply div_mul_cancel_right₀ htne0 2
      _ = ‖u₁ - u‖ ^ 2 / 2 := by
        rw [← mul_div_assoc,mul_one]
  rw [← this] at h₈
  have : t * σ u₁ + t * (‖u₁ - u‖ ^ 2 / (2 * t)) + t * ⟪u₁ - u, h' u⟫_ℝ
        = t * (σ u₁ + ‖u₁ - u‖ ^ 2 / (2 * t) + ⟪u₁ - u, h' u⟫_ℝ) := by ring
  rw [this] at h₈
  have hne : ⟪u₁ - u, h' u⟫_ℝ ≤ σ u - σ u₁ - ‖u₁ - u‖ ^ 2 / (2 * t) := by
    linarith [(mul_le_mul_left h₅).1 h₈]
  rw [real_inner_comm] at hne
  have hlip2 := lipschitz_continuos_upper_bound' h₁ h₂
  specialize hlip2 u u₁
  calc
    _ ≤ h u + ⟪h' u, u₁ - u⟫_ℝ + ↑Lₕ / 2 * ‖u₁ - u‖ ^ 2 + σ u₁ := by linarith [hlip2]
    _ ≤ h u + σ u - σ u₁ - ‖u₁ - u‖ ^ 2 / (2 * t) + ↑Lₕ / 2 * ‖u₁ - u‖ ^ 2 + σ u₁ := by linarith[hne]
    _ = h u + σ u - ‖u₁ - u‖ ^ 2 / (2 * t) + ↑Lₕ / 2 * ‖u₁ - u‖ ^ 2 := by linarith
    _ = h u + σ u - (1/ (2 * t) - ↑Lₕ / 2) * ‖u₁ - u‖ ^ 2 := by
      ring
    _ = h u + σ u - 1 / 2 * (1 / t - ↑Lₕ) * ‖u₁ - u‖ ^ 2 := by
      have : (1/ (2 * t) - ↑Lₕ / 2) = 1 / 2 * (1 / t - ↑Lₕ) := by
        have : 1 / (2 * t) = (1 / 2) * (1 / t) := by field_simp [htne0]
        rw[this]; ring
      rw [this]

/- sufficient descent -/
theorem Sufficient_Descent1
  (bd : Bornology.IsBounded (alg.z '' univ)) : ∃ ρ₁ > 0, ρ₁ = (γ - 1) * l ∧
  ∀ k, ρ₁ / 2 * ‖alg.z (k+1) - alg.z k‖ ^ 2 ≤ alg.ψ (alg.z k) -alg.ψ (alg.z (k + 1)) := by
  use (γ - 1) * l
  let ρ₁ := (γ - 1) * l
  have ργL : ρ₁ = (γ - 1) * l := rfl
  constructor; obtain hl := alg.lpos; apply mul_pos; linarith; exact hl;
  constructor; rfl
  have hz : ∃ M, ∀ (k: ℕ), ‖alg.z k‖ ≤ M := by
    rcases Bornology.IsBounded.exists_norm_le bd with ⟨M, hM⟩
    use M; intro k; specialize hM (alg.z k); simp at hM; exact hM
  have Hass : (∀ (y : F) , LipschitzWith l (grad_fst H y)) ∧ (∀ (x : E) , LipschitzWith l (grad_snd H x))
    := @ass_coordinate_lip E F _ _ _ _ _ _ f g H x0 y0 l alg
  obtain ⟨hfstlip, hsndlip⟩ := Hass
  intro k
  have hHf : H (alg.x (k + 1), alg.y k) + f (alg.x (k + 1))
            ≤ H (alg.x k, alg.y k) + f (alg.x k)
            - 1/2 * (γ - 1) * l * ‖alg.x (k + 1) - alg.x k‖^2 :=
    calc
      _ ≤ H (alg.x k, alg.y k) + f (alg.x k) - 1/2 *
            (1/alg.c k - l)  * ‖alg.x (k + 1) - alg.x k‖^2 := by
          let h := fun x ↦ H (x,alg.y k)
          let h':= fun x ↦ grad_fst H (alg.y k) x
          have h1: ∀ x₁ : E, HasGradientAt h (h' x₁) x₁ := by
            intro x
            have : h' x = gradient h x := by
              simp [h',grad_fst]
            rw [this]
            sorry

          have h2: LipschitzWith l h' := by
            specialize hfstlip (alg.y k)
            simp [h']
            exact hfstlip
          have h3: LowerSemicontinuous f := alg.hf
          have h4: ∃ (M : ℝ), ∀ (x : E) , f x ≥ M := by
            have :=alg.lbdf
            simp [BddBelow,lowerBounds,Set.Nonempty] at this
            rcases this with ⟨M,hM⟩
            use M
          have h5: 0 <(alg.c k) := by
            specialize ck k
            rw[ck]
            apply div_pos
            norm_num
            apply mul_pos
            linarith[hγ]
            apply alg.lpos
          have h55:γ * l - l = (γ - 1 ) * l := by
                rw[sub_mul,one_mul]
          have h6: (alg.c k) < 1 / l := by
            specialize ck k
            rw[ck]
            have neq1: 0 < γ * l := by
              apply mul_pos
              linarith[hγ]
              apply alg.lpos
            have neq2: 0 < l := by
              apply alg.lpos
            apply (one_div_lt_one_div neq1 neq2).2
            simp
            apply sub_pos.1
            rw [h55]
            apply mul_pos
            linarith[hγ]
            apply alg.lpos
          have prop :=PALM_Descent h l h1 h2 f (alg.c k) h5
          specialize prop (alg.x k) (alg.x (k+1))
          have h7 : alg.x (k + 1) ∈ prox_set (fun a ↦ alg.c k * f a) (alg.x k - alg.c k • h' (alg.x k)) :=by
              have h8 :=alg.s₁
              specialize h8 k
              rw[prox_set]
              simp
              have : (fun a ↦ alg.c k * f a)= alg.c k • f := by
                ext x
                simp
              rw[this]
              exact h8
          specialize prop h7
          simp only [h] at prop
          exact prop
      _ = H (alg.x k, alg.y k) + f (alg.x k)
            - 1/2 * (γ - 1) * l * ‖alg.x (k + 1) - alg.x k‖^2 := by
            rw [ck]
            have : 1 / (1 / (γ * l)) = γ * l := by
              apply one_div_one_div
            rw[this]
            have : γ * l - l = (γ - 1) * l := by ring
            rw[this]
            ring

  have hHg : H (alg.x (k + 1), alg.y (k + 1)) + g (alg.y (k + 1))
            ≤ H (alg.x (k + 1), alg.y k) + g (alg.y k)
            - 1/2 * (γ - 1) * l * ‖alg.y (k + 1) - alg.y k‖^2 :=
    calc
      H (alg.x (k + 1), alg.y (k + 1)) + g (alg.y (k + 1))
            ≤ H (alg.x (k + 1), alg.y k) + g (alg.y k)
            - 1/2 * (1/alg.d k - l)  * ‖alg.y (k + 1) - alg.y k‖^2 := by
          let h := fun y ↦ H (alg.x (k+1),y)
          let h':= fun y ↦ grad_snd H (alg.x (k+1)) y
          have h1 : ∀ y₁ : F, HasGradientAt h (h' y₁) y₁ := by
            intro y
            have : h' y = gradient h y := by
              simp [h',grad_snd]
            rw [this]
            sorry

          have h2: LipschitzWith l h' := by
            specialize hsndlip (alg.x (k+1))
            simp [h']
            exact hsndlip
          have h3: LowerSemicontinuous g := alg.hg
          have h4: ∃ (M : ℝ), ∀ (y : F) , g y ≥ M := by
            have :=alg.lbdg
            simp [BddBelow,lowerBounds,Set.Nonempty] at this
            rcases this with ⟨M,hM⟩
            use M
          have h5: 0 <(alg.d k) := by
            specialize ck k
            rw[dk]
            apply div_pos
            norm_num
            apply mul_pos
            linarith[hγ]
            apply alg.lpos
          have h55:γ * l - l = (γ - 1 ) * l := by
                rw[sub_mul,one_mul]
          have h6: (alg.d k) < 1 / l := by
            specialize ck k
            rw[dk]
            have neq1: 0 < γ * l := by
              apply mul_pos
              linarith[hγ]
              apply alg.lpos
            have neq2: 0 < l := by
              apply alg.lpos
            apply (one_div_lt_one_div neq1 neq2).2
            simp
            apply sub_pos.1
            rw [h55]
            apply mul_pos
            linarith[hγ]
            apply alg.lpos
          have prop :=PALM_Descent h l h1 h2 g (alg.d k) h5
          specialize prop (alg.y k) (alg.y (k+1))
          have h7 : alg.y (k + 1) ∈ prox_set (fun a ↦ alg.d k * g a)
              (alg.y k - alg.d k • h' (alg.y k)) :=by
            have h8 :=alg.s₂
            specialize h8 k
            rw[prox_set]
            simp
            have : (fun a ↦ alg.d k * g a)= alg.d k • g := by
              ext x
              simp
            rw[this]
            simp[h']
            exact h8
          specialize prop h7
          simp only [h] at prop
          exact prop
      _ = H (alg.x (k + 1), alg.y k) + g (alg.y k)
            - 1/2 * (γ - 1) * l * ‖alg.y (k + 1) - alg.y k‖^2 := by
            rw [dk]
            have : 1 / (1 / (γ * l)) = γ * l := by
              apply one_div_one_div
            rw[this]
            have : γ * l - l = (γ - 1) * l := by ring
            rw[this]
            ring

  have hPhi : alg.ψ (alg.z k) - alg.ψ (alg.z (k + 1))
              ≥ ρ₁ / 2 * ‖alg.z (k + 1) - alg.z k‖^2 :=
    calc
      alg.ψ (alg.z k) - alg.ψ (alg.z (k + 1)) = H (alg.x k, alg.y k) + f (alg.x k) + g (alg.y k)
        - H (alg.x (k + 1), alg.y (k + 1)) - f (alg.x (k + 1)) - g (alg.y (k + 1)) := by
        have eq1: alg.ψ (alg.z k) = H (alg.x k, alg.y k) + f (alg.x k) + g (alg.y k) := by
          rw[BCD.ψ]
          have : f (alg.z k).1 = f (alg.x k) := by
            rw[BCD.z]
            simp
          rw [this]
          have : g (alg.z k).2 = g (alg.y k) := by
            rw[BCD.z]
            simp
          rw [this]
          nth_rw 2 [add_assoc]
          nth_rw 1 [add_comm]
          apply add_right_cancel_iff.2
          have : alg.z k = (alg.x k, alg.y k) := by
            apply Prod.ext
            simp
            rw [BCD.z]
            apply WithLp.equiv_fst
            simp
            rw [BCD.z]
            apply WithLp.equiv_snd
          rw[this]
        have eq2: alg.ψ (alg.z (k+1)) = H (alg.x (k+1), alg.y (k+1)) + f (alg.x (k+1)) + g (alg.y (k+1)) := by
          rw[BCD.ψ]
          have : f (alg.z (k+1)).1 = f (alg.x (k+1)) := by
            rw[BCD.z]
            simp
          rw [this]
          have : g (alg.z (k+1)).2 = g (alg.y (k+1)) := by
            rw[BCD.z]
            simp
          rw [this]
          nth_rw 2 [add_assoc]
          nth_rw 1 [add_comm]
          apply add_right_cancel_iff.2
          have : alg.z (k+1) = (alg.x (k+1), alg.y (k+1)) := by
            apply Prod.ext
            simp
            rw [BCD.z]
            apply WithLp.equiv_fst
            simp
            rw [BCD.z]
            apply WithLp.equiv_snd
          rw[this]
        rw[eq1,eq2]
        ring
      _ ≥ 1/2 * (γ - 1) * l * (‖alg.x (k + 1) - alg.x k‖^2 + ‖alg.y (k + 1) - alg.y k‖^2) := by
        linarith [hHf,hHg]
      _ = 1/2 * ρ₁ * (‖alg.x (k + 1) - alg.x k‖^2 + ‖alg.y (k + 1) - alg.y k‖^2) := by
        rw[ργL]
        nth_rw 2 [mul_assoc]
      _ = 1/2 * ρ₁ * ‖alg.z (k + 1) - alg.z k‖^2 := by
        simp only [WithLp.prod_norm_sq_eq_of_L2]
        have :(alg.z (k + 1) - alg.z k).1 =(alg.z (k + 1)).1 - (alg.z k).1 := by
          apply Prod.fst_sub
        rw[this]
        have :(alg.z (k + 1) - alg.z k).2 =(alg.z (k + 1)).2 - (alg.z k).2 := by
          apply Prod.snd_sub
        rw[this]
        rw[BCD.z]
        rw[BCD.z]
        simp
      _ = ρ₁ / 2 * ‖alg.z (k + 1) - alg.z k‖^2 := by
        have :1/2 * ρ₁ = ρ₁ / 2 :=by ring
        rw[this]
  exact hPhi


/- the value is monotone -/
theorem Sufficient_Descent2 (bd : Bornology.IsBounded (alg.z '' univ)) :
    ∀ (k : ℕ), alg.ψ (alg.z (k+1)) ≤ alg.ψ (alg.z k) := by
  rcases Sufficient_Descent1 γ hγ ck dk bd with ⟨ρ₁, ⟨hρ₁, ⟨_, h2⟩⟩⟩
  intro k; specialize h2 k
  have hne : 0 ≤ ρ₁ / 2 * ‖alg.z (k + 1) - alg.z k‖^2  := by positivity
  linarith

/- The difference series squares are summable-/
theorem Sufficient_Descent3 (bd : Bornology.IsBounded (alg.z '' univ))
  (lbdψ : BddBelow (alg.ψ '' univ)) :
  ∃ (A : ℝ), Tendsto (series_sum (fun k ↦ ‖alg.z (k + 1) -alg.z k‖^2)) atTop (𝓝 A) := by
  rcases Sufficient_Descent1 γ hγ ck dk bd with ⟨ρ₁, ⟨hρ₁, ⟨ργL, h2⟩⟩⟩
  have lpos: l > (0 : ℝ ) := alg.lpos
  have hρ₁ : 2 / ρ₁ ≥  0 := by positivity
  have hDescent' : ∀ k, ‖alg.z (k + 1) - alg.z k‖ ^ 2
      ≤ 2 / ρ₁ * (alg.ψ (alg.z k) - alg.ψ (alg.z (k + 1))):= by
    intro k
    specialize h2 k
    have h1:=mul_le_mul_of_nonneg_left h2 hρ₁
    rw [← mul_assoc] at h1
    have :2 / ρ₁ * (ρ₁ / 2) = 1 := by
      ring_nf
      apply mul_inv_cancel
      rw [ργL]
      apply mul_ne_zero
      linarith[hγ]
      linarith[lpos]
    rw [this] at h1
    rw [one_mul] at h1
    exact h1
  have hne : ∀ n, series_sum (fun (k : ℕ ) ↦ ‖alg.z (k+1) -alg.z k‖^2) (n+1)
      ≤ 2 / ρ₁ * ((alg.ψ (alg.z 0) ) -( alg.ψ (alg.z (n+1)))) := by
    intro n
    induction' n with d hd
    simp
    rw [series_sum]
    simp [Finset.sum_range_succ]
    specialize hDescent' 0
    simp at hDescent'
    exact hDescent'
    rw [series_sum]
    have : ∀ (d : ℕ) ,∑ k ∈ Finset.range (d + 1), ‖alg.z (k + 1) - alg.z k‖ ^ 2
        = ∑ k ∈ Finset.range d, ‖alg.z (k + 1) - alg.z k‖ ^ 2 + ‖alg.z (d + 1) - alg.z d‖ ^ 2 := by
        intro d
        simp [Finset.sum_range_succ]
    rw [series_sum] at hd
    rw [this (d+1)]
    have : 2 / ρ₁ * (alg.ψ (alg.z 0) - alg.ψ (alg.z (d + 1 + 1)))
          =  2 / ρ₁ * (alg.ψ (alg.z 0) - alg.ψ (alg.z (d + 1)))
          + 2 / ρ₁ * (alg.ψ (alg.z (d + 1)) - alg.ψ (alg.z (d + 1 + 1))) := by
          linarith
    rw [this]
    specialize hDescent' (d+1)
    apply add_le_add hd hDescent'
  simp [BddBelow,lowerBounds,Set.Nonempty] at lbdψ
  rcases lbdψ with ⟨ψ₀,hψ₀⟩
  have hne' : ∀ n : ℕ ,series_sum ( fun (k : ℕ ) ↦ ‖alg.z (k+1) -alg.z k‖^2 ) (n+1)
                    ≤ 2 / ρ₁ *( ( alg.ψ (alg.z 0) )- ψ₀ ) := by
      intro n
      specialize hne n
      specialize hψ₀ (alg.z (n+1))
      have h2: alg.ψ (alg.z 0) - alg.ψ (alg.z (n + 1)) ≤ alg.ψ (alg.z 0) - ψ₀:= by
        linarith [hψ₀]
      have h3:=mul_le_mul_of_nonneg_left h2 hρ₁
      apply le_trans hne h3
  let S := (fun (n : ℕ)↦ series_sum ( fun (k : ℕ ) ↦ ‖alg.z (k+1) -alg.z k‖^2 ) n)
  have : S = series_sum fun k ↦ ‖alg.z (k + 1) - alg.z k‖ ^ 2 := by
    apply funext
    intro x
    simp [S]
  rw [← this]
  rw [← this] at hne'
  have hne'': ∀ n ≥ 1, S n ≤ 2 / ρ₁ * (alg.ψ (alg.z 0) - ψ₀) := by
    intros n nge1
    specialize hne' (n-1)
    have : n - 1 + 1 = n :=by
      exact Nat.sub_add_cancel nge1
    rw [this] at hne'
    exact hne'
  set M₁ := max (S 0) (2 / ρ₁ * (alg.ψ (alg.z 0) - ψ₀)) with hₘ
  have lbdS: ∀ (n : ℕ) , S n ≤ M₁ := by
    rw[hₘ]
    intro n
    by_cases h0: n = 0
    apply le_max_iff.2
    left
    rw[h0]
    apply le_max_iff.2
    right
    apply Nat.pos_of_ne_zero at h0
    have h1:n ≥ 1 :=by linarith [h0]
    specialize hne'' n h1
    exact hne''
  have hge0: ∀ (n : ℕ), 0 ≤ ‖alg.z (n + 1) - alg.z n‖ ^ 2 := by
    intro n
    rw [pow_two]
    apply mul_nonneg
    apply norm_nonneg
    apply norm_nonneg
  have hlbd: ∀ (n : ℕ), ∑ i ∈ Finset.range n, ‖alg.z (i + 1) - alg.z i‖ ^ 2 ≤ M₁ := by
    simp [S,series_sum] at lbdS
    exact lbdS
  have hSum: Summable (fun (k : ℕ )↦ ‖alg.z (k + 1) - alg.z k‖ ^ 2) := by
    apply summable_of_sum_range_le hge0 hlbd
  simp [Summable] at hSum
  rcases hSum with ⟨a,ha⟩
  have hA:= HasSum.tendsto_sum_nat ha
  use a
  simp [S,series_sum]
  exact hA

/- the difference squence tends to 0 -/
theorem Sufficient_Descent4 (bd : Bornology.IsBounded (alg.z '' univ)) (lbdψ : BddBelow (alg.ψ '' univ)):
    Tendsto (fun k ↦ ‖alg.z (k+1) - alg.z k‖) atTop (𝓝 0) :=by
  rcases Sufficient_Descent3 γ hγ ck dk bd lbdψ with ⟨A, hA⟩
  have eq: ∀ n, ‖alg.z (n + 1) - alg.z n‖^2 = (series_sum (fun k ↦ ‖alg.z (k + 1) - alg.z k‖ ^ 2) (n+1))
      - (series_sum (fun k ↦ ‖alg.z (k + 1) - alg.z k‖ ^ 2) n) := by
    intro n
    rw [series_sum]
    rw [series_sum]
    simp [Finset.sum_range_succ]
  simp [series_sum] at eq
  rw [Metric.tendsto_atTop] at hA
  simp [dist_eq_norm] at hA
  simp [series_sum] at hA
  rw [Metric.tendsto_atTop]
  simp [dist_zero_right]
  have SqConver : ∀ (ε : ℝ), 0 < ε → ∃ N, ∀ (n : ℕ), N ≤ n → ‖alg.z (n + 1) - alg.z n‖^2 < ε := by
    intro ε εge0
    specialize hA (ε / 2)
    have εhalfge0 : 0 < ε / 2 := by linarith[εge0]
    have εhalf :∃ N, ∀ (n : ℕ), N ≤ n → |∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A| < ε / 2
    := by exact hA εhalfge0
    rcases εhalf with ⟨N,hNεhalf⟩
    use N
    intro n ngeN
    have eq':‖ alg.z (n + 1) - alg.z n‖ ^ 2 =
        (∑ k ∈ Finset.range (n + 1), ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A )
      - (∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2 -A ) := by
      rw[sub_sub_sub_comm]
      simp
      specialize eq n
      exact eq
    rw[eq']
    have hNεhalf':|∑ k ∈ Finset.range (n+1), ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A| < ε / 2 := by
      have ngeN': N ≤ n + 1 := by linarith[ngeN]
      specialize hNεhalf (n+1) ngeN'
      exact hNεhalf
    have hNεhalf1:∑ k ∈ Finset.range (n+1), ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A < ε / 2 := by
      rw [abs_lt] at hNεhalf'
      exact hNεhalf'.right
    have hNεhalf2: ∑ k ∈ Finset.range n, ‖alg.z (k + 1) - alg.z k‖ ^ 2 - A > -(ε / 2) := by
      specialize hNεhalf n ngeN
      rw [abs_lt] at hNεhalf
      exact hNεhalf.left
    linarith[hNεhalf1,hNεhalf1]
  intro ε εge0
  have εsqge0: 0 < ε * ε  := by
    apply mul_pos εge0 εge0
  rw [← pow_two] at εsqge0
  set εsq := ε ^ 2 with sqeq
  specialize SqConver εsq εsqge0
  rw [sqeq] at SqConver
  rcases SqConver with ⟨N,hN⟩
  use N
  intro n ngeN
  specialize hN n ngeN
  set a := ‖alg.z (n + 1) - alg.z n‖ with algeq
  have neq : |a| < |ε| := by
    apply sq_lt_sq.1 hN
  have eq1 : |ε| = ε := by
    apply abs_of_pos εge0
  have age0 : 0 ≤ a := by
    rw[algeq]
    apply norm_nonneg
  have eq2 : |a| = a := by
    apply abs_of_nonneg age0
  rw [eq1,eq2] at neq
  exact neq

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

instance ProS : ProperSpace (WithLp 2 (E × F)):= by sorry

lemma limitset_property_1 (bd : Bornology.IsBounded (alg.z '' univ)) :
    (limit_set alg.z).Nonempty ∧ ( (limit_set alg.z) ⊆ critial_point alg.ψ) := by
  sorry

lemma limitset_property_2 (bd : Bornology.IsBounded (alg.z '' univ)):
    Tendsto (fun n ↦ (EMetric.infEdist (alg.z n) (limit_set alg.z)).toReal) atTop (𝓝 0) := by
  sorry

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
