import AcceleratedLogConcave.Analysis.Poisson.TransportedGraph
import AcceleratedLogConcave.Analysis.Poisson.MovingForms

/-!
# The centered closed graph as the actual common Hilbert domain
-/
noncomputable section
open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace
namespace AcceleratedLogConcave.Analysis.Poisson
open WeightedGradient

section Abstract
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
variable (D : H →ₗ.[ℝ] K) (ell : H →L[ℝ] ℝ)

/-- Scalar inclusion of the actual centered closed graph. -/
def referenceGraphValue : centeredGraph D ell →L[ℝ] H :=
  (WithLp.fstL 2 ℝ H K).comp (centeredGraph D ell).subtypeL

/-- Gradient coordinate of the actual centered closed graph. -/
def referenceGraphGradient : centeredGraph D ell →L[ℝ] K :=
  (WithLp.sndL 2 ℝ H K).comp (centeredGraph D ell).subtypeL

def referenceGraphSobolev (u : centeredGraph D ell) : D.domain :=
  ⟨referenceGraphValue D ell u, LinearPMap.mem_domain_of_mem_graph u.property.1⟩

theorem referenceGraphGradient_eq (u : centeredGraph D ell) :
    referenceGraphGradient D ell u = D (referenceGraphSobolev D ell u) := by
  exact D.mem_graph_snd_inj u.property.1 (D.mem_graph (referenceGraphSobolev D ell u)) rfl

theorem referenceGraphValue_centered (u : centeredGraph D ell) :
    ell (referenceGraphValue D ell u) = 0 := u.property.2

/-- Every centered domain element is represented in the genuine graph. -/
def referenceGraphLift (u : D.domain) (hu : ell u = 0) : centeredGraph D ell :=
  ⟨WithLp.toLp 2 ((u : H), D u), ⟨D.mem_graph u, hu⟩⟩

@[simp] theorem referenceGraphLift_value (u : D.domain) (hu : ell u = 0) :
    referenceGraphValue D ell (referenceGraphLift D ell u hu) = (u : H) := rfl

@[simp] theorem referenceGraphLift_gradient (u : D.domain) (hu : ell u = 0) :
    referenceGraphGradient D ell (referenceGraphLift D ell u hu) = D u := rfl

/-- Poincare coercivity in the true graph Hilbert norm. -/
theorem referenceGraph_coercive {m : ℝ} (hm : 0 < m)
    (hP : ∀ u : D.domain, ell u = 0 → m * ‖(u : H)‖ ^ 2 ≤ ‖D u‖ ^ 2)
    (u : centeredGraph D ell) :
    (m / (m + 1)) * ‖u‖ ^ 2 ≤ ‖referenceGraphGradient D ell u‖ ^ 2 := by
  have hp := hP (referenceGraphSobolev D ell u) (referenceGraphValue_centered D ell u)
  have hn : ‖u‖ ^ 2 = ‖referenceGraphValue D ell u‖ ^ 2 +
      ‖referenceGraphGradient D ell u‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 _
  change m * ‖referenceGraphValue D ell u‖ ^ 2 ≤ ‖D (referenceGraphSobolev D ell u)‖ ^ 2 at hp
  rw [← referenceGraphGradient_eq] at hp
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < m + 1)]
  nlinarith

/-- A bounded inverse of the gradient coefficient gives uniform coercivity
of the actual transported form on the same centered graph. -/
theorem referenceGraph_multiplier_coercive {m B : ℝ} (hm : 0 < m) (hB : 0 < B)
    (hP : ∀ u : D.domain, ell u = 0 → m * ‖(u : H)‖ ^ 2 ≤ ‖D u‖ ^ 2)
    (A J : K →L[ℝ] K) (hJA : ∀ v, J (A v) = v) (hJ : ‖J‖ ≤ B)
    (u : centeredGraph D ell) :
    (m / (m + 1) / B ^ 2) * ‖u‖ ^ 2 ≤ ‖(A.comp (referenceGraphGradient D ell)) u‖ ^ 2 := by
  have hp := referenceGraph_coercive D ell hm hP u
  have hn : ‖referenceGraphGradient D ell u‖ ≤ B * ‖A (referenceGraphGradient D ell u)‖ := by
    calc
      _ = ‖J (A (referenceGraphGradient D ell u))‖ := congrArg norm (hJA _).symm
      _ ≤ _ := J.le_of_opNorm_le hJ _
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB.le (norm_nonneg _))).mpr hn
  change _ ≤ ‖A (referenceGraphGradient D ell u)‖ ^ 2
  rw [div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hB)]
  nlinarith
end Abstract
end AcceleratedLogConcave.Analysis.Poisson
