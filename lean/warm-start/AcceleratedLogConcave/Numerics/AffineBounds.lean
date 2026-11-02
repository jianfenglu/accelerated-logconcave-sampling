import AcceleratedLogConcave.Numerics.AffineGraph
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import AcceleratedLogConcave.Numerics.GeometricMesh
import AcceleratedLogConcave.Gibbs.PrimitiveMoments
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual affine row bounds and primitive-mean Lipschitz adapters

Bounds are derived from the actual coefficient forms, retaining shared rotation
terms before absolute values. The L² adapter assumes measurability of the raw
states and square integrability only of their differences. Common raw anchors
cancel pointwise. The final λ and λr bounds compose the output rows with actual
primitive means at fixed positive radii. Stationary residuals, stochastic
couplings, recursive compilation, query costs and sampler accuracy are separate.
-/

noncomputable section AffineBoundsRows
open scoped BigOperators
open MeasureTheory

namespace AcceleratedLogConcave.Numerics.AffineGraph
open GaussLegendre ReciprocalQuadrature

namespace IntervalMesh
variable {lo hi : ℝ} (M : IntervalMesh lo hi)

theorem clipped_mem (t : ℝ) (c : M.Cell) :
    M.clipped t c ∈ Set.Icc (M.left c) (M.right c) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (le_of_lt (sub_pos.mp (M.length_pos c))) (min_le_right _ _)

def normalizedCoordinate (t : ℝ) (c : M.Cell) : ℝ :=
  (M.clipped t c - M.left c) / M.length c

theorem normalizedCoordinate_mem (t : ℝ) (c : M.Cell) :
    M.normalizedCoordinate t c ∈ Set.Icc (0 : ℝ) 1 := by
  have h := M.clipped_mem t c
  constructor
  · exact div_nonneg (sub_nonneg.mpr h.1) (M.length_pos c).le
  · apply (div_le_one (M.length_pos c)).mpr
    simpa only [length] using sub_le_sub_right h.2 (M.left c)

theorem left_add_length_mul_normalizedCoordinate (t : ℝ) (c : M.Cell) :
    M.left c + M.length c * M.normalizedCoordinate t c = M.clipped t c := by
  unfold normalizedCoordinate
  rw [mul_div_cancel₀ _ (ne_of_gt (M.length_pos c))]
  ring

theorem row_eq_partialRow (m : ℕ) (u v : ℝ) (z : M.Source m) :
    M.row m u v z = partialRow m (M.left z.1) (M.length z.1)
      (M.normalizedCoordinate u z.1) (M.normalizedCoordinate v z.1)
      (fun _ => 1) z.2 := by
  have hc : Continuous (fun y : ℝ =>
      (cardinal m z.2).eval ((y - M.left z.1) / M.length z.1)) :=
    (cardinal m z.2).continuous.comp ((continuous_id.sub continuous_const).div_const _)
  rw [row, M.cumulative_eq_integral, M.cumulative_eq_integral,
    intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  simp only [partialRow, one_mul, M.left_add_length_mul_normalizedCoordinate]

theorem sum_length : (∑ c : M.Cell, M.length c) = hi - lo := by
  have hfirst := Fin.sum_univ_succ M.point
  have hlast := Fin.sum_univ_castSucc M.point
  simp only [M.first] at hfirst
  simp only [M.last] at hlast
  simp only [length, right, left, Finset.sum_sub_distrib]
  linarith

theorem sum_abs_row_le (m : ℕ) (hm : 0 < m) (u v : ℝ) :
    (∑ z : M.Source m, |M.row m u v z|) ≤ hi - lo := by
  rw [Fintype.sum_prod_type, ← M.sum_length]
  apply Finset.sum_le_sum
  intro c _
  simp_rw [M.row_eq_partialRow]
  exact sum_abs_partialRow_le_length m hm (M.left c) (M.length c)
    (M.normalizedCoordinate u c) (M.normalizedCoordinate v c) (M.length_pos c)
    (M.normalizedCoordinate_mem u c) (M.normalizedCoordinate_mem v c) (fun _ => 1)
    aestronglyMeasurable_const (Filter.Eventually.of_forall (fun _ => by norm_num))

theorem sum_cellWeights (m : ℕ) (hm : 0 < m) :
    (∑ z : M.Source m, cellWeight m (M.length z.1) z.2) = hi - lo := by
  rw [Fintype.sum_prod_type]
  simp_rw [sum_cellWeight m hm]
  exact M.sum_length

theorem sum_abs_row_endpoints (m : ℕ) (hm : 0 < m) :
    (∑ z : M.Source m, |M.row m lo hi z|) = hi - lo := by
  simp_rw [M.row_endpoints, abs_of_nonneg
    (cellWeight_nonneg m _ _ (M.length_pos _).le)]
  exact M.sum_cellWeights m hm
end IntervalMesh

namespace MeanGeometry
variable {m : ℕ}

theorem centerNode_mem (b : Fin m) : centerNode b ∈ Set.Ioo (0 : ℝ) 1 := by
  simpa only [centerNode, zero_add] using
    cellNode_mem_Ioo m 0 1 (by norm_num) b

theorem sum_abs_centerRow_le (m : ℕ) (hm : 0 < m) (a : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (∑ b : Fin m, |centerRow a b|) ≤ 1 := by
  exact sum_abs_partialRow_le_length m hm 0 1 0 a (by norm_num)
    (by norm_num) ha (fun _ => 1) aestronglyMeasurable_const
    (Filter.Eventually.of_forall (fun _ => by norm_num))

variable (G : MeanGeometry m)

theorem angleNode_mem (z : Fin m) : G.angleNode z ∈ Set.Ioo (0 : ℝ) G.psi := by
  simpa only [angleNode, zero_add] using cellNode_mem_Ioo m 0 G.psi G.psi_pos z

theorem sum_abs_backRow_le (hm : 0 < m) (a : ℝ) :
    (∑ j : G.backward.Source m, |G.backRow a j|) ≤ backwardEnd G.R := by
  simpa only [backRow, sub_zero] using
    G.backward.sum_abs_row_le m hm (backwardEnd G.R) a

theorem sum_abs_condRow_le (hm : 0 < m) (ρ : G.Kernel) (η : ℝ) :
    (∑ j : (G.conditional ρ).Source m, |G.condRow ρ η j|) ≤ conditionalEnd := by
  simpa only [condRow, sub_zero] using (G.conditional ρ).sum_abs_row_le m hm 0 η

theorem sum_abs_forwRow_le (hm : 0 < m) (ρ : G.Kernel) (a : ℝ) :
    (∑ j : (G.forward ρ).Source m, |G.forwRow ρ a j|) ≤ backwardEnd G.R - G.rho ρ := by
  exact (G.forward ρ).sum_abs_row_le m hm (G.rho ρ) a

theorem sum_abs_angleDerivative_le :
    (∑ z : Fin m, |G.angleDerivative z|) ≤ (m : ℝ)^3 / G.psi := by
  exact sum_abs_derivativeRow_le m 0 G.psi 0 G.psi_pos
    ⟨le_rfl, by linarith [G.psi_pos]⟩

theorem sum_abs_meanOutput_weights (hm : 0 < m) :
    (∑ b : Fin m, |weight m b|) = 1 := by
  simp_rw [abs_of_nonneg (weight_pos m _).le]
  exact sum_weight m hm
end MeanGeometry

namespace SamplingGeometry
variable {m : ℕ} (S : SamplingGeometry m)

theorem sum_abs_row_le (hm : 0 < m) (a : ℝ) :
    (∑ j : S.Node, |S.row a j|) ≤ samplingEnd S.τ := by
  simpa only [row, sub_zero] using S.mesh.sum_abs_row_le m hm 0 a

theorem sum_abs_output_weights (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    (∑ j : S.Node, |-(r / samplingEnd S.τ) * S.row (samplingEnd S.τ) j|) = r := by
  simp_rw [abs_mul, abs_neg, abs_of_nonneg (div_nonneg hr S.samplingEnd_pos.le)]
  rw [← Finset.mul_sum]
  have hsum := S.mesh.sum_abs_row_endpoints m hm
  change (∑ j : S.Node, |S.row (samplingEnd S.τ) j|) = samplingEnd S.τ - 0 at hsum
  rw [hsum, sub_zero, div_mul_cancel₀ _ S.samplingEnd_pos.ne']

section Vector
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem sum_abs_matrix_le (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) (x y0 : E)
    (i : S.Node) : (∑ j : S.Node, |(S.graph r x y0).matrix i j|) ≤ r^2 := by
  have ha := S.mesh.location_mem_interval m i
  have ha1 : S.mesh.location m i ≤ 1 := ha.2.le.trans S.samplingEnd_lt_one.le
  simp only [graph, abs_mul, abs_neg, abs_of_nonneg hr, abs_of_nonneg ha.1.le]
  rw [← Finset.mul_sum]
  calc
    r * S.mesh.location m i * r * (∑ j : S.Node, |S.row (S.mesh.location m i) j|)
      ≤ r * S.mesh.location m i * r * samplingEnd S.τ :=
        mul_le_mul_of_nonneg_left (S.sum_abs_row_le hm _)
          (mul_nonneg (mul_nonneg hr ha.1.le) hr)
    _ = r^2 * (S.mesh.location m i * samplingEnd S.τ) := by ring
    _ ≤ r^2 * 1 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
      exact (mul_le_mul_of_nonneg_right ha1 S.samplingEnd_pos.le).trans
        (by simpa using S.samplingEnd_lt_one.le)
    _ = r^2 := mul_one _
end Vector
end SamplingGeometry

end AcceleratedLogConcave.Numerics.AffineGraph
end AffineBoundsRows

noncomputable section AffineBoundsMatrix
open scoped BigOperators
open Set
namespace AcceleratedLogConcave.Numerics.AffineGraph
open GaussLegendre ReciprocalQuadrature
namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)

def ellRot (ρ : G.Kernel) (z : ℝ) : ℝ :=
  1 - (G.rotationScale ρ)^2 * (1 - Real.cos (z / G.rotationScale ρ))
def seedRot (ρ : G.Kernel) (z : ℝ) : ℝ :=
  G.rho ρ * Real.sqrt (2 * G.variance ρ) / (1 + (G.rho ρ)^2) *
    (1 - Real.cos (z / G.rotationScale ρ))
def scoreRot (ρ : G.Kernel) (z : ℝ) : ℝ :=
  G.rotationScale ρ * Real.sin (z / G.rotationScale ρ)

/-- Collect the shared backward and conditional forms before taking any norms. -/
theorem rotationForm_eq (r σ : ℝ) (b : Fin m) (ρ : G.Kernel) (z : ℝ) :
    G.rotationForm r σ b ρ z =
      G.ellRot ρ z • G.backwardForm r σ b (G.rho ρ) +
      G.seedRot ρ z • G.conditionalForm r b ρ conditionalEnd +
      G.scoreRot ρ z • G.scoreForm σ (centerNode b) := by
  have hs : Real.sqrt (G.variance ρ) / conditionalEnd = Real.sqrt (2 * G.variance ρ) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp [conditionalEnd, mul_comm]
  simp only [rotationForm, midpointForm, observationForm, ellRot, seedRot, scoreRot]
  rw [hs, G.rotationScale_sq]
  unfold variance
  match_scalars <;> field_simp <;> ring

theorem ellRot_abs_le_one (ρ : G.Kernel) (z : ℝ) : |G.ellRot ρ z| ≤ 1 := by
  have hq : (G.rotationScale ρ)^2 ≤ 1 := by
    rw [G.rotationScale_sq]
    apply (div_le_one (by positivity)).mpr
    unfold variance
    nlinarith [sq_nonneg (G.rho ρ)]
  have hc := Real.cos_le_one (z / G.rotationScale ρ)
  have hc' := Real.neg_one_le_cos (z / G.rotationScale ρ)
  have hq0 := sq_nonneg (G.rotationScale ρ)
  unfold ellRot
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hc),
    mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hc)]

theorem scoreRot_abs_le (ρ : G.Kernel) (z : ℝ) (hz : 0 ≤ z) :
    |G.scoreRot ρ z| ≤ z := by
  rw [scoreRot, abs_mul, abs_of_pos (G.rotationScale_pos ρ)]
  calc
    _ ≤ G.rotationScale ρ * |z / G.rotationScale ρ| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (G.rotationScale_pos ρ).le
    _ = z := by
      rw [abs_of_nonneg (div_nonneg hz (G.rotationScale_pos ρ).le)]
      field_simp [(G.rotationScale_pos ρ).ne']

theorem seedRot_nonneg (ρ : G.Kernel) (z : ℝ) : 0 ≤ G.seedRot ρ z := by
  exact mul_nonneg (div_nonneg (mul_nonneg (G.rho_mem ρ).1 (Real.sqrt_nonneg _))
    (by positivity)) (sub_nonneg.mpr (Real.cos_le_one _))

theorem seedRot_scaled_eq (ρ : G.Kernel) (z : ℝ) :
    G.seedRot ρ z * Real.sqrt (G.variance ρ) * conditionalEnd =
      G.rho ρ * (G.rotationScale ρ)^2 * (1 - Real.cos (z / G.rotationScale ρ)) := by
  rw [seedRot, G.rotationScale_sq, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hv := Real.sq_sqrt (G.variance_pos ρ).le
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  unfold conditionalEnd
  field_simp
  rw [hv]
  ring

theorem seedRot_scaled_le_sq (ρ : G.Kernel) (z : ℝ) :
    G.seedRot ρ z * Real.sqrt (G.variance ρ) * conditionalEnd ≤ z^2 := by
  rw [G.seedRot_scaled_eq]
  have hc := Real.one_sub_sq_div_two_le_cos (x := z / G.rotationScale ρ)
  have hq := G.rotationScale_pos ρ
  have hrho := (G.rho_mem ρ).1
  have hrho1 := (G.rho_mem ρ).2.trans G.backwardEnd_lt_one
  have he : (G.rotationScale ρ)^2 * ((z / G.rotationScale ρ)^2 / 2) = z^2/2 := by
    field_simp [hq.ne']
  have hb := mul_le_mul_of_nonneg_left (show 1 - Real.cos (z / G.rotationScale ρ) ≤
    (z / G.rotationScale ρ)^2/2 by linarith) (sq_nonneg (G.rotationScale ρ))
  rw [he] at hb
  have hb' := mul_le_mul_of_nonneg_left hb hrho
  nlinarith [sq_nonneg z]

def meanCoefficientMass (L : Form G.Atom) : ℝ := ∑ j : G.MeanNode, |L (G.meanAtom j)|

theorem meanCoefficientMass_nonneg (L : Form G.Atom) : 0 ≤ G.meanCoefficientMass L :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

@[simp] theorem meanCoefficientMass_zero : G.meanCoefficientMass 0 = 0 := by
  simp [meanCoefficientMass]

@[simp] theorem meanCoefficientMass_meanAtom (i : G.MeanNode) :
    G.meanCoefficientMass (Form.atom (G.meanAtom i)) = 1 := by
  classical
  simp only [meanCoefficientMass, Form.atom, meanAtom, Sum.inr.injEq,
    abs_ite, abs_one, abs_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

@[simp] theorem meanCoefficientMass_anchor (a : G.Anchor) :
    G.meanCoefficientMass (Form.atom (.inl a)) = 0 := by
  simp [meanCoefficientMass, Form.atom, meanAtom]

theorem meanCoefficientMass_add (L H : Form G.Atom) :
    G.meanCoefficientMass (L+H) ≤ G.meanCoefficientMass L + G.meanCoefficientMass H := by
  simp only [meanCoefficientMass, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_add_le _ _)

theorem meanCoefficientMass_sub (L H : Form G.Atom) :
    G.meanCoefficientMass (L-H) ≤ G.meanCoefficientMass L + G.meanCoefficientMass H := by
  simp only [meanCoefficientMass, Pi.sub_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_sub _ _)

theorem meanCoefficientMass_smul (c : ℝ) (L : Form G.Atom) :
    G.meanCoefficientMass (c • L) = |c| * G.meanCoefficientMass L := by
  simp only [meanCoefficientMass, Pi.smul_apply, smul_eq_mul, abs_mul, Finset.mul_sum]

theorem meanCoefficientMass_sum {κ : Type*} [Fintype κ] (L : κ → Form G.Atom) :
    G.meanCoefficientMass (∑ k, L k) ≤ ∑ k, G.meanCoefficientMass (L k) := by
  classical
  simp only [meanCoefficientMass, Finset.sum_apply]
  exact (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)).trans_eq
    (Finset.sum_comm)

theorem meanCoefficientMass_sum_smul_le {κ : Type*} [Fintype κ]
    (c : κ → ℝ) (L : κ → Form G.Atom) (B : ℝ)
    (hL : ∀ k, G.meanCoefficientMass (L k) ≤ B) :
    G.meanCoefficientMass (∑ k, c k • L k) ≤ (∑ k, |c k|) * B := by
  apply (G.meanCoefficientMass_sum _).trans
  simp_rw [G.meanCoefficientMass_smul]
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hL k) (abs_nonneg _))

theorem meanCoefficientMass_sum_atoms_le {κ : Type*} [Fintype κ]
    (c : κ → ℝ) (i : κ → G.MeanNode) :
    G.meanCoefficientMass (∑ k, c k • Form.atom (G.meanAtom (i k))) ≤ ∑ k, |c k| := by
  simpa using G.meanCoefficientMass_sum_smul_le c (fun k => Form.atom (G.meanAtom (i k))) 1
    (fun _ => (G.meanCoefficientMass_meanAtom _).le)

def kernelMass : ℝ := ∑ ρ : G.Kernel, |G.kernelCoeff ρ|
def velocityMassBound (σ : ℝ) : ℝ := 2 * G.kernelMass * (m:ℝ)^3 / (σ * G.psi)

theorem kernelMass_nonneg : 0 ≤ G.kernelMass := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
theorem velocityMassBound_nonneg (σ : ℝ) (hs : 0 < σ) : 0 ≤ G.velocityMassBound σ := by
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) G.kernelMass_nonneg) (by positivity))
    (mul_pos hs G.psi_pos).le

theorem meanCoefficientMass_velocityForm (hm : 0 < m) (σ : ℝ) (hs : 0 < σ)
    (b : Fin m) : G.meanCoefficientMass (G.velocityForm σ b) ≤ G.velocityMassBound σ := by
  have hi (ρ : G.Kernel) (z : Fin m) : G.meanCoefficientMass
      (∑ j : (G.forward ρ).Source m, G.forwRow ρ (backwardEnd G.R) j •
        Form.atom (G.meanAtom (.forward G b ρ z j))) ≤ 1 := by
    apply (G.meanCoefficientMass_sum_atoms_le _ _).trans
    exact (G.sum_abs_forwRow_le hm ρ _).trans (by linarith [(G.rho_mem ρ).1, G.backwardEnd_lt_one])
  have ha (ρ : G.Kernel) : G.meanCoefficientMass
      (∑ z : Fin m, G.angleDerivative z • ∑ j : (G.forward ρ).Source m,
        G.forwRow ρ (backwardEnd G.R) j • Form.atom (G.meanAtom (.forward G b ρ z j))) ≤
      (m:ℝ)^3 / G.psi := by
    exact (G.meanCoefficientMass_sum_smul_le _ _ 1 (hi ρ)).trans
      (by simpa only [mul_one] using G.sum_abs_angleDerivative_le)
  have hk := G.meanCoefficientMass_sum_smul_le G.kernelCoeff _ ((m:ℝ)^3 / G.psi) ha
  rw [velocityForm, G.meanCoefficientMass_smul, abs_of_pos (inv_pos.mpr (div_pos hs (by norm_num)))]
  apply (mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr (div_nonneg hs.le (by norm_num)))).trans_eq
  unfold velocityMassBound kernelMass
  field_simp

theorem meanCoefficientMass_positionForm (hm : 0 < m) (σ : ℝ) (hs : 0 < σ)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) :
    G.meanCoefficientMass (G.positionForm σ a) ≤ G.velocityMassBound σ := by
  apply (G.meanCoefficientMass_add _ _).trans
  rw [show G.meanCoefficientMass (Form.atom G.positionAtom) = 0 from G.meanCoefficientMass_anchor _, zero_add]
  exact (G.meanCoefficientMass_sum_smul_le _ _ _ (G.meanCoefficientMass_velocityForm hm σ hs)).trans
    ((mul_le_mul_of_nonneg_right (sum_abs_centerRow_le m hm a ha)
      (G.velocityMassBound_nonneg σ hs)).trans_eq (one_mul _))

theorem meanCoefficientMass_scoreForm (hm : 0 < m) (σ : ℝ) (hs : 0 < σ)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) :
    G.meanCoefficientMass (G.scoreForm σ a) ≤ 4 / σ := by
  have hd (b : Fin m) : G.meanCoefficientMass
      (Form.atom (G.meanAtom (.center G b)) - Form.atom (G.meanAtom (.base G))) ≤ 2 := by
    simpa only [G.meanCoefficientMass_meanAtom, one_add_one_eq_two] using G.meanCoefficientMass_sub
      (Form.atom (G.meanAtom (.center G b))) (Form.atom (G.meanAtom (.base G)))
  have hsum := (G.meanCoefficientMass_sum_smul_le _ _ 2 hd).trans
    (mul_le_mul_of_nonneg_right (sum_abs_centerRow_le m hm a ha) (by norm_num))
  apply (G.meanCoefficientMass_add _ _).trans
  rw [show G.meanCoefficientMass (Form.atom G.scoreAtom) = 0 from G.meanCoefficientMass_anchor _, zero_add,
    G.meanCoefficientMass_smul, abs_of_pos (inv_pos.mpr (div_pos hs (by norm_num)))]
  apply (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (div_nonneg hs.le (by norm_num)))).trans_eq
  field_simp
  ring

theorem meanCoefficientMass_backwardForm (hm : 0 < m) (r σ : ℝ) (hr : 0 ≤ r)
    (hs : 0 < σ) (b : Fin m) (a : ℝ) :
    G.meanCoefficientMass (G.backwardForm r σ b a) ≤ G.velocityMassBound σ + r * backwardEnd G.R := by
  apply (G.meanCoefficientMass_sub _ _).trans
  rw [G.meanCoefficientMass_smul, abs_of_nonneg hr]
  apply add_le_add (G.meanCoefficientMass_positionForm hm σ hs _
    ⟨(centerNode_mem b).1.le, (centerNode_mem b).2.le⟩)
  exact mul_le_mul_of_nonneg_left ((G.meanCoefficientMass_sum_atoms_le _ _).trans
    (G.sum_abs_backRow_le hm a)) hr

theorem meanCoefficientMass_conditionalForm (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r)
    (b : Fin m) (ρ : G.Kernel) (η : ℝ) :
    G.meanCoefficientMass (G.conditionalForm r b ρ η) ≤ r * Real.sqrt (G.variance ρ) * conditionalEnd := by
  apply (G.meanCoefficientMass_sub _ _).trans
  rw [show G.meanCoefficientMass (Form.atom (G.seedAtom b ρ)) = 0 from G.meanCoefficientMass_anchor _, zero_add,
    G.meanCoefficientMass_smul, abs_of_nonneg (mul_nonneg hr (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left ((G.meanCoefficientMass_sum_atoms_le _ _).trans
    (G.sum_abs_condRow_le hm ρ η)) (mul_nonneg hr (Real.sqrt_nonneg _))

theorem meanCoefficientMass_rotationForm (hm : 0 < m) (r σ : ℝ) (hr : 0 ≤ r)
    (hs : 0 < σ) (b : Fin m) (ρ : G.Kernel) (z : Fin m) :
    G.meanCoefficientMass (G.rotationForm r σ b ρ (G.angleNode z)) ≤
      G.velocityMassBound σ + r * backwardEnd G.R + r * G.psi^2 + 4 * G.psi / σ := by
  have he : |G.ellRot ρ (G.angleNode z)| *
      G.meanCoefficientMass (G.backwardForm r σ b (G.rho ρ)) ≤
      G.velocityMassBound σ + r * backwardEnd G.R := by
    exact ((mul_le_mul_of_nonneg_right (G.ellRot_abs_le_one ρ _)
      (G.meanCoefficientMass_nonneg _)).trans_eq (one_mul _)).trans
      (G.meanCoefficientMass_backwardForm hm r σ hr hs b _)
  have hc : |G.seedRot ρ (G.angleNode z)| *
      G.meanCoefficientMass (G.conditionalForm r b ρ conditionalEnd) ≤ r * G.psi^2 := by
    rw [abs_of_nonneg (G.seedRot_nonneg ρ _)]
    calc
      _ ≤ G.seedRot ρ (G.angleNode z) * (r * Real.sqrt (G.variance ρ) * conditionalEnd) :=
        mul_le_mul_of_nonneg_left (G.meanCoefficientMass_conditionalForm hm r hr b ρ _)
          (G.seedRot_nonneg ρ _)
      _ = r * (G.seedRot ρ (G.angleNode z) * Real.sqrt (G.variance ρ) * conditionalEnd) := by ring
      _ ≤ r * (G.angleNode z)^2 := mul_le_mul_of_nonneg_left (G.seedRot_scaled_le_sq ρ _) hr
      _ ≤ r * G.psi^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (G.angleNode_mem z).1.le (G.angleNode_mem z).2.le 2) hr
  have hg : |G.scoreRot ρ (G.angleNode z)| *
      G.meanCoefficientMass (G.scoreForm σ (centerNode b)) ≤ 4 * G.psi / σ := by
    calc
      _ ≤ G.angleNode z * (4 / σ) := mul_le_mul
        (G.scoreRot_abs_le ρ _ (G.angleNode_mem z).1.le)
        (G.meanCoefficientMass_scoreForm hm σ hs _ ⟨(centerNode_mem b).1.le, (centerNode_mem b).2.le⟩)
        (G.meanCoefficientMass_nonneg _) (G.angleNode_mem z).1.le
      _ ≤ G.psi * (4 / σ) := mul_le_mul_of_nonneg_right (G.angleNode_mem z).2.le (by positivity)
      _ = _ := by ring
  rw [G.rotationForm_eq]
  apply (G.meanCoefficientMass_add _ _).trans
  apply (add_le_add (G.meanCoefficientMass_add _ _) le_rfl).trans
  simp only [G.meanCoefficientMass_smul]
  linarith

theorem meanCoefficientMass_forwardForm (hm : 0 < m) (r σ : ℝ) (hr : 0 ≤ r)
    (hs : 0 < σ) (hpsi : G.psi ≤ 1) (b : Fin m) (ρ : G.Kernel) (z : Fin m) (a : ℝ) :
    G.meanCoefficientMass (G.forwardForm r σ b ρ z a) ≤
      G.velocityMassBound σ + 3*r + 4*G.psi/σ := by
  apply (G.meanCoefficientMass_sub _ _).trans
  rw [G.meanCoefficientMass_smul, abs_of_nonneg hr]
  have hc := (G.meanCoefficientMass_sum_atoms_le _ (fun j => MeanNode.forward G b ρ z j)).trans
    (G.sum_abs_forwRow_le hm ρ a)
  have hb := add_le_add (G.meanCoefficientMass_rotationForm hm r σ hr hs b ρ z)
    (mul_le_mul_of_nonneg_left hc hr)
  apply hb.trans
  have hpsi2 : G.psi^2 ≤ 1 := by nlinarith [G.psi_pos]
  have hp := mul_le_mul_of_nonneg_left hpsi2 hr
  have hβ := mul_le_mul_of_nonneg_left G.backwardEnd_lt_one.le hr
  have hρ := mul_nonneg hr (G.rho_mem ρ).1
  nlinarith

theorem matrix_sqrt_variance_le_one (ρ : G.Kernel) : Real.sqrt (G.variance ρ) ≤ 1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · unfold variance
    nlinarith [sq_nonneg (G.rho ρ)]

theorem meanCoefficientMass_conditionalForm_le_r (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r)
    (b : Fin m) (ρ : G.Kernel) (η : ℝ) :
    G.meanCoefficientMass (G.conditionalForm r b ρ η) ≤ r := by
  apply (G.meanCoefficientMass_conditionalForm hm r hr b ρ η).trans
  have h := mul_le_mul (G.matrix_sqrt_variance_le_one ρ) conditionalEnd_lt_one.le
    conditionalEnd_pos.le (by norm_num : (0:ℝ) ≤ 1)
  nlinarith [mul_le_mul_of_nonneg_left h hr]

theorem sum_abs_matrix_le_kernelMass (hm : 2 ≤ m) (r σ : ℝ) (hr : 0 ≤ r)
    (hs : 0 < σ) (hpsi : G.psi ≤ 1) (i : G.MeanNode) :
    (∑ j, |G.matrix r σ i j|) ≤
      2*r*(∑ ρ : G.Kernel, |G.kernelCoeff ρ|)*(m:ℝ)^3/(σ*G.psi) +
        4*r*G.psi/σ + 3*r^2 := by
  have hm0 : 0 < m := by omega
  have hV := G.velocityMassBound_nonneg σ hs
  have hψ := G.psi_pos
  have hS : 0 ≤ 4*G.psi/σ := by positivity
  have hSr : 0 ≤ 4*r*G.psi/σ := by positivity
  have targetEq : r * G.velocityMassBound σ + 4*r*G.psi/σ + 3*r^2 =
      2*r*(∑ ρ : G.Kernel, |G.kernelCoeff ρ|)*(m:ℝ)^3/(σ*G.psi) +
        4*r*G.psi/σ + 3*r^2 := by unfold velocityMassBound kernelMass; ring
  rw [← targetEq]
  change G.meanCoefficientMass (G.centerForm r σ i) ≤ _
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · simp only [centerForm, G.meanCoefficientMass_zero]
    positivity
  · rw [centerForm, G.meanCoefficientMass_smul, abs_of_nonneg (mul_nonneg hr G.backwardEnd_pos.le)]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left G.backwardEnd_lt_one.le hr)
      (G.meanCoefficientMass_positionForm hm0 σ hs _ ⟨(centerNode_mem b).1.le, (centerNode_mem b).2.le⟩)
      (G.meanCoefficientMass_nonneg _) (by simpa only [mul_one] using hr)
    nlinarith [sq_nonneg r]
  · have ha := G.backward.location_mem_interval m j
    rw [centerForm, G.meanCoefficientMass_smul, abs_of_nonneg (mul_nonneg hr ha.1.le)]
    have hb := (G.meanCoefficientMass_backwardForm hm0 r σ hr hs b (G.backward.location m j)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left G.backwardEnd_lt_one.le hr))
    have h := mul_le_mul (mul_le_mul_of_nonneg_left (ha.2.trans G.backwardEnd_lt_one).le hr)
      hb (G.meanCoefficientMass_nonneg _) (by simpa only [mul_one] using hr)
    nlinarith [sq_nonneg r]
  · have hη := (G.conditional ρ).location_mem_interval m j
    have hρ := G.rho_mem ρ
    have hc : r * Real.sqrt (G.variance ρ) * (G.conditional ρ).location m j ≤ r := by
      have h := mul_le_mul (G.matrix_sqrt_variance_le_one ρ)
        (hη.2.trans conditionalEnd_lt_one).le hη.1.le (by norm_num : (0:ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_left h hr]
    rw [centerForm]
    apply (G.meanCoefficientMass_add _ _).trans
    rw [G.meanCoefficientMass_smul, G.meanCoefficientMass_smul,
      abs_of_nonneg (mul_nonneg hr hρ.1),
      abs_of_nonneg (mul_nonneg (mul_nonneg hr (Real.sqrt_nonneg _)) hη.1.le)]
    have hb := (G.meanCoefficientMass_backwardForm hm0 r σ hr hs b (G.rho ρ)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left G.backwardEnd_lt_one.le hr))
    have h1 := mul_le_mul (mul_le_mul_of_nonneg_left (hρ.2.trans G.backwardEnd_lt_one).le hr)
      hb (G.meanCoefficientMass_nonneg _) (by simpa only [mul_one] using hr)
    have h2 := mul_le_mul hc (G.meanCoefficientMass_conditionalForm_le_r hm0 r hr b ρ ((G.conditional ρ).location m j))
      (G.meanCoefficientMass_nonneg _) hr
    nlinarith [sq_nonneg r]
  · have ha := (G.forward ρ).location_mem_interval m j
    have ha0 := (G.rho_mem ρ).1.trans ha.1.le
    rw [centerForm, G.meanCoefficientMass_smul, abs_of_nonneg (mul_nonneg hr ha0)]
    have h := mul_le_mul (mul_le_mul_of_nonneg_left (ha.2.trans G.backwardEnd_lt_one).le hr)
      (G.meanCoefficientMass_forwardForm hm0 r σ hr hs hpsi b ρ z ((G.forward ρ).location m j))
      (G.meanCoefficientMass_nonneg _) (by simpa only [mul_one] using hr)
    exact h.trans_eq (by ring)

/-- The actual reciprocal coefficient theorem supplies the sole mesh estimate. -/
theorem kernelMass_le_of_firstWidth (hm : 2 ≤ m) (h₀ : ℝ) (hh : 0 < h₀)
    (hfirst : h₀/4 ≤ G.backward.length 0) :
    G.kernelMass ≤ 40*(m:ℝ)^2/h₀ := by
  exact sum_abs_kernelValueCoefficient_le m hm G.backward.point G.backward.strictMono
    G.backward.first h₀ hh hfirst

theorem sum_abs_matrix_le (hm : 2 ≤ m) (r σ : ℝ) (hr : 0 ≤ r) (hs : 0 < σ)
    (hpsi : G.psi ≤ 1) (h₀ : ℝ) (hh : 0 < h₀) (hhupper : h₀ ≤ 1/2)
    (hfirst : h₀/4 ≤ G.backward.length 0) (i : G.MeanNode) :
    (∑ j, |G.matrix r σ i j|) ≤ 256*(m:ℝ)^5*r/(σ*G.psi*h₀) + 4*r^2 := by
  have hψ := G.psi_pos
  have hden : 0 < σ*G.psi*h₀ := by positivity
  have hk := G.kernelMass_le_of_firstWidth hm h₀ hh hfirst
  have hterm : 2*r*G.kernelMass*(m:ℝ)^3/(σ*G.psi) ≤
      80*(m:ℝ)^5*r/(σ*G.psi*h₀) := by
    calc
      _ ≤ 2*r*(40*(m:ℝ)^2/h₀)*(m:ℝ)^3/(σ*G.psi) := by gcongr
      _ = _ := by field_simp; ring
  have hunit : G.psi^2*h₀ ≤ (m:ℝ)^5 := by
    have hp : G.psi^2 ≤ 1 := by nlinarith
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hm5 := one_le_pow₀ hm1 (n := 5)
    have h := mul_le_mul_of_nonneg_right hp hh.le
    nlinarith
  have hsmall : 4*r*G.psi/σ ≤ 4*(m:ℝ)^5*r/(σ*G.psi*h₀) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ = (4*r)*(G.psi^2*h₀) := by field_simp
      _ ≤ (4*r)*(m:ℝ)^5 := mul_le_mul_of_nonneg_left hunit (by positivity)
      _ = _ := by ring
  have hA : 0 ≤ (m:ℝ)^5*r/(σ*G.psi*h₀) := by positivity
  have h := G.sum_abs_matrix_le_kernelMass hm r σ hr hs hpsi i
  change (∑ j, |G.matrix r σ i j|) ≤
    2*r*G.kernelMass*(m:ℝ)^3/(σ*G.psi) + 4*r*G.psi/σ + 3*r^2 at h
  calc
    _ ≤ 80*(m:ℝ)^5*r/(σ*G.psi*h₀) + 4*(m:ℝ)^5*r/(σ*G.psi*h₀) + 3*r^2 :=
      h.trans (add_le_add (add_le_add hterm hsmall) le_rfl)
    _ = 84*((m:ℝ)^5*r/(σ*G.psi*h₀)) + 3*r^2 := by ring
    _ ≤ 256*((m:ℝ)^5*r/(σ*G.psi*h₀)) + 4*r^2 := by nlinarith [sq_nonneg r]
    _ = _ := by ring

end MeanGeometry
end AcceleratedLogConcave.Numerics.AffineGraph
end AffineBoundsMatrix

noncomputable section AffineBoundsKernel
open scoped BigOperators
namespace AcceleratedLogConcave.Numerics.AffineGraph
open GaussLegendre ReciprocalQuadrature

/-- The actual kernel partition, with no supplied coefficient or first-width bound. -/
def actualKernelInterval (R h₀ : ℝ) (hR : 0 < R) (hRupper : R ≤ 1 / 2)
    (hh : 0 < h₀) : IntervalMesh 0 (backwardEnd R) where
  cellsPred := GeometricMesh.cellCount 0 (Real.sqrt (1 - R ^ 2)) h₀ - 1
  point := GeometricMesh.kernelMesh R h₀
  strictMono := GeometricMesh.kernelMesh_strictMono hR hRupper hh
  first := GeometricMesh.kernelMesh_zero R h₀
  last := GeometricMesh.kernelMesh_horizon hR hRupper hh

/-- Actual first-cell lower bound, derived from the chosen geometric partition. -/
theorem actualKernelInterval_firstCell_lower {R h₀ : ℝ} (hR : 0 < R)
    (hRupper : R ≤ 1 / 2) (hh : 0 < h₀) (hhupper : h₀ ≤ 1 / 2) :
    h₀ / 4 ≤ (actualKernelInterval R h₀ hR hRupper hh).length 0 := by
  exact GeometricMesh.kernelMesh_firstCell_lower hR hRupper hh hhupper

/-- The chosen mesh proves its complete signed kernel mass, including the origin. -/
theorem actualKernelInterval_kernel_mass_le (m : ℕ) (hm : 2 ≤ m)
    {R h₀ : ℝ} (hR : 0 < R) (hRupper : R ≤ 1 / 2) (hh : 0 < h₀)
    (hhupper : h₀ ≤ 1 / 2) :
    (∑ ρ, |kernelValueCoefficient m
      (actualKernelInterval R h₀ hR hRupper hh).point ρ|) ≤
      40 * (m : ℝ) ^ 2 / h₀ := by
  exact GeometricMesh.kernel_coefficient_mass_le m hm hR hRupper hh hhupper

/-- The selected backward partition with independent conditional and forward meshes. -/
def actualMeanGeometry (m : ℕ) (R h₀ ψ : ℝ) (hR : 0 < R)
    (hRupper : R ≤ 1 / 2) (hh : 0 < h₀) (hψ : 0 < ψ)
    (conditional : (ρ : Option ((actualKernelInterval R h₀ hR hRupper hh).Source m)) →
      IntervalMesh 0 conditionalEnd)
    (forward : (ρ : Option ((actualKernelInterval R h₀ hR hRupper hh).Source m)) →
      IntervalMesh
        (kernelValueLocation m (actualKernelInterval R h₀ hR hRupper hh).point ρ)
        (backwardEnd R)) : MeanGeometry m where
  R := R
  R_pos := hR
  R_le_half := hRupper
  psi := ψ
  psi_pos := hψ
  backward := actualKernelInterval R h₀ hR hRupper hh
  conditional := conditional
  forward := forward

namespace MeanGeometry

/-- For the selected backward mesh, the geometric first-width theorem discharges
all quantitative mesh premises. Only the actual partition identity is supplied. -/
theorem sum_abs_matrix_le_actual {m : ℕ} (G : MeanGeometry m) (hm : 2 ≤ m)
    (r σ : ℝ) (hr : 0 ≤ r) (hs : 0 < σ) (hpsi : G.psi ≤ 1)
    (h₀ : ℝ) (hh : 0 < h₀) (hhupper : h₀ ≤ 1 / 2)
    (hback : G.backward = actualKernelInterval G.R h₀ G.R_pos G.R_le_half hh)
    (i : G.MeanNode) :
    (∑ j, |G.matrix r σ i j|) ≤
      256 * (m : ℝ) ^ 5 * r / (σ * G.psi * h₀) + 4 * r ^ 2 := by
  have hfirst : h₀ / 4 ≤ G.backward.length 0 := by
    rw [hback]
    exact actualKernelInterval_firstCell_lower G.R_pos G.R_le_half hh hhupper
  exact G.sum_abs_matrix_le hm r σ hr hs hpsi h₀ hh hhupper hfirst i

end MeanGeometry

/-- The concrete constructor's actual matrix bound, with no kernel-mass,
first-cell or matrix estimate among the assumptions. -/
theorem actualMeanGeometry_sum_abs_matrix_le (m : ℕ) (hm : 2 ≤ m)
    (R h₀ ψ : ℝ) (hR : 0 < R) (hRupper : R ≤ 1 / 2)
    (hh : 0 < h₀) (hhupper : h₀ ≤ 1 / 2) (hψ : 0 < ψ) (hψupper : ψ ≤ 1)
    (conditional : (ρ : Option ((actualKernelInterval R h₀ hR hRupper hh).Source m)) →
      IntervalMesh 0 conditionalEnd)
    (forward : (ρ : Option ((actualKernelInterval R h₀ hR hRupper hh).Source m)) →
      IntervalMesh
        (kernelValueLocation m (actualKernelInterval R h₀ hR hRupper hh).point ρ)
        (backwardEnd R))
    (r σ : ℝ) (hr : 0 ≤ r) (hs : 0 < σ)
    (i : (actualMeanGeometry m R h₀ ψ hR hRupper hh hψ conditional forward).MeanNode) :
    (∑ j, |(actualMeanGeometry m R h₀ ψ hR hRupper hh hψ conditional forward).matrix r σ i j|) ≤
      256 * (m : ℝ) ^ 5 * r / (σ * ψ * h₀) + 4 * r ^ 2 := by
  exact (actualMeanGeometry m R h₀ ψ hR hRupper hh hψ conditional forward).sum_abs_matrix_le_actual
    hm r σ hr hs hψupper h₀ hh hhupper rfl i

end AcceleratedLogConcave.Numerics.AffineGraph
end AffineBoundsKernel

noncomputable section AffineBoundsShapes
namespace AcceleratedLogConcave.Numerics.AffineGraph

namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)

theorem backwardEnd_sq : (backwardEnd G.R)^2 = 1 - G.R^2 := by
  apply Real.sq_sqrt
  have h := mul_self_le_mul_self G.R_pos.le G.R_le_half
  nlinarith

theorem sqrt_radius_lower {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ backwardEnd G.R) :
    G.R ≤ Real.sqrt (1 - a^2) := by
  apply Real.le_sqrt_of_sq_le
  have h := mul_self_le_mul_self ha hab
  nlinarith [G.backwardEnd_sq]

theorem variance_lower (ρ : G.Kernel) : G.R^2 ≤ G.variance ρ := by
  have hρ := G.rho_mem ρ
  have h := mul_self_le_mul_self hρ.1 hρ.2.le
  dsimp [variance]
  nlinarith [G.backwardEnd_sq]

theorem rotationScale_upper (ρ : G.Kernel) : G.rotationScale ρ ≤ 1 := by
  have hd : 0 < 1 + (G.rho ρ)^2 := by positivity
  have hsq : (G.rotationScale ρ)^2 ≤ 1 := by
    rw [G.rotationScale_sq]
    apply (div_le_one₀ hd).mpr
    dsimp [variance]
    nlinarith [sq_nonneg (G.rho ρ)]
  nlinarith

theorem rotationScale_lower (ρ : G.Kernel) : G.R / Real.sqrt 2 ≤ G.rotationScale ρ := by
  have hρ := G.rho_mem ρ
  have hρ1 : G.rho ρ ≤ 1 := hρ.2.le.trans G.backwardEnd_lt_one.le
  have hden : 1 + (G.rho ρ)^2 ≤ 2 := by
    have h := mul_self_le_mul_self hρ.1 hρ1
    nlinarith
  have hd : 1 + (G.rho ρ)^2 ≠ 0 := by positivity
  have he := (eq_div_iff hd).mp (G.rotationScale_sq ρ)
  have hmul := mul_le_mul_of_nonneg_left hden (sq_nonneg (G.rotationScale ρ))
  have hsq : G.R^2 ≤ 2 * (G.rotationScale ρ)^2 := by
    linarith [G.variance_lower ρ]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))).mpr
  apply le_of_sq_le_sq _ (mul_nonneg (G.rotationScale_pos ρ).le (Real.sqrt_nonneg 2))
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), mul_comm] using hsq

theorem psi_div_rotationScale_le (hpsi : G.psi ≤ G.R^4) (ρ : G.Kernel) :
    G.psi / G.rotationScale ρ ≤ Real.sqrt 2 * G.R^3 := by
  have hq := (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))).mp
    (G.rotationScale_lower ρ)
  have hmul := mul_le_mul_of_nonneg_left hq (pow_nonneg G.R_pos.le 3)
  apply (div_le_iff₀ (G.rotationScale_pos ρ)).mpr
  nlinarith

theorem angleNode_bounds (z : Fin m) : 0 ≤ G.angleNode z ∧ G.angleNode z ≤ G.psi := by
  have h := GaussLegendre.cellNode_mem_Ioo m 0 G.psi G.psi_pos z
  constructor
  · exact h.1.le
  · simpa only [angleNode, zero_add] using h.2.le

theorem rotation_loss_bounds (ρ : G.Kernel) (z : Fin m) :
    0 ≤ (G.rotationScale ρ)^2 * (1 - Real.cos (G.angleNode z / G.rotationScale ρ)) ∧
    (G.rotationScale ρ)^2 * (1 - Real.cos (G.angleNode z / G.rotationScale ρ)) ≤
      G.psi^2 / 2 := by
  have hq := G.rotationScale_pos ρ
  have hz := G.angleNode_bounds z
  constructor
  · exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (Real.cos_le_one _))
  have hcos : 1 - Real.cos (G.angleNode z / G.rotationScale ρ) ≤
      (G.angleNode z / G.rotationScale ρ)^2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := G.angleNode z / G.rotationScale ρ)]
  have hmul := mul_le_mul_of_nonneg_left hcos (sq_nonneg (G.rotationScale ρ))
  have he : (G.rotationScale ρ)^2 * ((G.angleNode z / G.rotationScale ρ)^2 / 2) =
      (G.angleNode z)^2 / 2 := by field_simp
  rw [he] at hmul
  have hzsq := mul_self_le_mul_self hz.1 hz.2
  nlinarith

/-- The coefficient of the original position anchor in the actual direct vector. -/
def positionCoeff : G.MeanNode → ℝ
  | .inl _ => 0
  | .inr (.inl _) => backwardEnd G.R
  | .inr (.inr (.inl (_,j))) => G.backward.location m j
  | .inr (.inr (.inr (.inl (_,⟨ρ,_⟩)))) => G.rho ρ
  | .inr (.inr (.inr (.inr (_,⟨ρ,z,j⟩)))) =>
      (G.forward ρ).location m j *
        (1 - (G.rotationScale ρ)^2 * (1 - Real.cos (G.angleNode z / G.rotationScale ρ)))

theorem direct_positionCoeff (r σ : ℝ) (i : G.MeanNode) :
    G.direct r σ (0 : ℝ) 1 0 (fun _ _ ↦ 0) i = r * G.positionCoeff i := by
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · simpa [positionCoeff, MeanNode.base] using
      G.direct_base r σ (0:ℝ) 1 0 (fun _ _ ↦ 0)
  · simpa [positionCoeff, MeanNode.center] using
      G.direct_center r σ (0:ℝ) 1 0 (fun _ _ ↦ 0) b
  · simpa [positionCoeff, MeanNode.backward] using
      G.direct_backward r σ (0:ℝ) 1 0 (fun _ _ ↦ 0) b j
  · simpa [positionCoeff, MeanNode.conditional] using
      G.direct_conditional r σ (0:ℝ) 1 0 (fun _ _ ↦ 0) b ρ j
  · simpa [positionCoeff, MeanNode.forward, mul_assoc] using
      G.direct_forward r σ (0:ℝ) 1 0 (fun _ _ ↦ 0) b ρ z j

def normalizedRadius (i : G.MeanNode) : ℝ := G.radius 1 i

theorem radius_eq_mul_normalizedRadius (r : ℝ) (i : G.MeanNode) :
    G.radius r i = r * G.normalizedRadius i := by
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩ <;>
    simp [radius, normalizedRadius, mul_assoc]

theorem radius_div_normalizedRadius (r : ℝ) (hr : 0 < r) (i : G.MeanNode) :
    G.radius r i / r = G.normalizedRadius i := by
  rw [G.radius_eq_mul_normalizedRadius]
  exact mul_div_cancel_left₀ _ hr.ne'

theorem normalizedRadius_pos (i : G.MeanNode) : 0 < G.normalizedRadius i :=
  G.radius_pos 1 (by norm_num) i

theorem conditional_normalizedRadius_lower (b : Fin m) (ρ : G.Kernel)
    (j : (G.conditional ρ).Source m) :
    Real.sqrt (G.variance ρ) / Real.sqrt 2 ≤
      G.normalizedRadius (.conditional G b ρ j) := by
  have hη := (G.conditional ρ).location_mem_interval m j
  have hηsq := mul_self_le_mul_self hη.1.le hη.2.le
  have he : conditionalEnd^2 = (1:ℝ)/2 := by
    norm_num [conditionalEnd, div_pow, Real.sq_sqrt]
  have hhalf : conditionalEnd ≤ Real.sqrt (1 - ((G.conditional ρ).location m j)^2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hhalf (Real.sqrt_nonneg (G.variance ρ))
  simpa [normalizedRadius, radius, MeanNode.conditional, conditionalEnd,
    div_eq_mul_inv] using hmul

theorem normalizedRadius_lower (i : G.MeanNode) :
    G.R / Real.sqrt 2 ≤ G.normalizedRadius i := by
  have htwo : (1:ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hden : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hR : G.R / Real.sqrt 2 ≤ G.R := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [G.R_pos]
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · simpa [normalizedRadius, radius] using hR.trans (G.R_le_half.trans (by norm_num))
  · simpa [normalizedRadius, radius] using hR
  · have h := G.backward.location_mem_interval m j
    simpa [normalizedRadius, radius] using hR.trans (G.sqrt_radius_lower h.1.le h.2.le)
  · have hv : G.R ≤ Real.sqrt (G.variance ρ) :=
      Real.le_sqrt_of_sq_le (G.variance_lower ρ)
    exact (div_le_div_of_nonneg_right hv hden.le).trans
      (G.conditional_normalizedRadius_lower b ρ j)
  · have h := (G.forward ρ).location_mem_interval m j
    simpa [normalizedRadius, radius] using hR.trans
      (G.sqrt_radius_lower ((G.rho_mem ρ).1.trans h.1.le) h.2.le)

theorem radius_lower (r : ℝ) (hr : 0 < r) (i : G.MeanNode) :
    r * G.R / Real.sqrt 2 ≤ G.radius r i := by
  rw [G.radius_eq_mul_normalizedRadius]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (G.normalizedRadius_lower i) hr.le

theorem psi_le_R (hpsi : G.psi ≤ G.R^4) : G.psi ≤ G.R := by
  have hR1 : G.R ≤ 1 := G.R_le_half.trans (by norm_num)
  have hp : G.R^3 ≤ 1 := pow_le_one₀ G.R_pos.le hR1
  have hmul := mul_le_mul_of_nonneg_left hp G.R_pos.le
  nlinarith

theorem positionCoeff_mem (hpsi : G.psi ≤ G.R^4) (i : G.MeanNode) :
    0 ≤ G.positionCoeff i ∧ G.positionCoeff i ≤ backwardEnd G.R := by
  have hpsi1 : G.psi ≤ 1 := (G.psi_le_R hpsi).trans (G.R_le_half.trans (by norm_num))
  have hpsisq : G.psi^2 ≤ 1 := pow_le_one₀ G.psi_pos.le hpsi1
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · exact ⟨le_rfl, G.backwardEnd_pos.le⟩
  · exact ⟨G.backwardEnd_pos.le, le_rfl⟩
  · exact ⟨(G.backward.location_mem_interval m j).1.le,
      (G.backward.location_mem_interval m j).2.le⟩
  · exact ⟨(G.rho_mem ρ).1, (G.rho_mem ρ).2.le⟩
  · have ha := (G.forward ρ).location_mem_interval m j
    have ha0 : 0 ≤ (G.forward ρ).location m j := (G.rho_mem ρ).1.trans ha.1.le
    have hd := G.rotation_loss_bounds ρ z
    dsimp [positionCoeff]
    constructor
    · exact mul_nonneg ha0 (by linarith)
    · calc
        _ ≤ (G.forward ρ).location m j * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [hd.1]) ha0
        _ ≤ backwardEnd G.R := by simpa only [mul_one] using ha.2.le

theorem position_defect_le_sqrt {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ backwardEnd G.R) :
    1 - a / backwardEnd G.R ≤ Real.sqrt (1 - a^2) := by
  have ha1 : a ≤ 1 := hab.trans G.backwardEnd_lt_one.le
  have hdiv : a ≤ a / backwardEnd G.R := by
    apply (le_div_iff₀ G.backwardEnd_pos).mpr
    exact (mul_le_mul_of_nonneg_left G.backwardEnd_lt_one.le ha).trans_eq (mul_one a)
  have hs : 1 - a ≤ Real.sqrt (1 - a^2) := by
    apply Real.le_sqrt_of_sq_le
    have hprod := mul_nonneg ha (sub_nonneg.mpr ha1)
    nlinarith
  linarith

theorem shift_shape_le (hpsi : G.psi ≤ G.R^4) (r : ℝ) (hr : 0 < r)
    (i : G.MeanNode) :
    |1 - G.positionCoeff i / backwardEnd G.R| / (G.radius r i / r) ≤ 3 := by
  rw [G.radius_div_normalizedRadius r hr i]
  apply (div_le_iff₀ (G.normalizedRadius_pos i)).mpr
  have hi := G.positionCoeff_mem hpsi i
  rw [abs_of_nonneg (sub_nonneg.mpr ((div_le_one₀ G.backwardEnd_pos).mpr hi.2))]
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · norm_num [positionCoeff, normalizedRadius, radius]
  · simp only [positionCoeff, normalizedRadius, radius, one_mul,
      div_self G.backwardEnd_pos.ne', sub_self]
    exact mul_nonneg (by norm_num) G.R_pos.le
  · have ha := G.backward.location_mem_interval m j
    have hdef := G.position_defect_le_sqrt ha.1.le ha.2.le
    dsimp [positionCoeff, normalizedRadius, radius]
    nlinarith [Real.sqrt_nonneg (1 - (G.backward.location m j)^2)]
  · have hρ := G.rho_mem ρ
    have hdef := G.position_defect_le_sqrt hρ.1 hρ.2.le
    have hcond := (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))).mp
      (G.conditional_normalizedRadius_lower b ρ j)
    have hsqrt : Real.sqrt 2 ≤ 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg 2]
    have hmul := mul_le_mul_of_nonneg_left hsqrt
      (G.normalizedRadius_pos (.conditional G b ρ j)).le
    change 1 - G.rho ρ / backwardEnd G.R ≤ 3 *
      G.normalizedRadius (.conditional G b ρ j)
    dsimp [variance] at hcond
    nlinarith
  · let a := (G.forward ρ).location m j
    let d := (G.rotationScale ρ)^2 * (1 - Real.cos (G.angleNode z / G.rotationScale ρ))
    have ha := (G.forward ρ).location_mem_interval m j
    have ha0 : 0 ≤ a := (G.rho_mem ρ).1.trans ha.1.le
    have hdef := G.position_defect_le_sqrt ha0 ha.2.le
    have hd := G.rotation_loss_bounds ρ z
    have hpsisq := mul_self_le_mul_self G.psi_pos.le (G.psi_le_R hpsi)
    have hRsq : G.R^2 ≤ G.R := by
      have h := mul_le_mul_of_nonneg_left
        (G.R_le_half.trans (by norm_num : (1:ℝ)/2 ≤ 1)) G.R_pos.le
      nlinarith
    have hdR : d ≤ G.R := by dsimp [d]; nlinarith [G.R_pos]
    have hdRad : d ≤ Real.sqrt (1 - a^2) :=
      hdR.trans (G.sqrt_radius_lower ha0 ha.2.le)
    have hprod : (a / backwardEnd G.R) * d ≤ d := by
      have h := mul_le_mul_of_nonneg_right
        ((div_le_one₀ G.backwardEnd_pos).mpr ha.2.le) hd.1
      simpa only [one_mul] using h
    change 1 - a * (1 - d) / backwardEnd G.R ≤ 3 * (1 * Real.sqrt (1 - a^2))
    have he : 1 - a * (1-d) / backwardEnd G.R =
        (1 - a / backwardEnd G.R) + (a / backwardEnd G.R) * d := by ring
    rw [he]
    nlinarith [Real.sqrt_nonneg (1 - a^2)]

end MeanGeometry
end AcceleratedLogConcave.Numerics.AffineGraph


namespace AcceleratedLogConcave.Numerics.AffineGraph.SamplingGeometry
variable {m : ℕ} (S : SamplingGeometry m)

def positionCoeff (j : S.Node) : ℝ := S.mesh.location m j

def normalizedRadius (i : S.Node) : ℝ := S.radius 1 i

theorem radius_eq_mul_normalizedRadius (r : ℝ) (i : S.Node) :
    S.radius r i = r * S.normalizedRadius i := by
  simp [normalizedRadius, radius]

theorem radius_div_normalizedRadius (r : ℝ) (hr : 0 < r) (i : S.Node) :
    S.radius r i / r = S.normalizedRadius i := by
  rw [S.radius_eq_mul_normalizedRadius]
  exact mul_div_cancel_left₀ _ (ne_of_gt hr)

theorem direct_positionCoeff (r : ℝ) (i : S.Node) :
    (S.graph r (0 : ℝ) 1).direct i = r * S.positionCoeff i := by
  simp [graph, positionCoeff]

theorem positionCoeff_mem (i : S.Node) :
    0 ≤ S.positionCoeff i ∧ S.positionCoeff i ≤ samplingEnd S.τ :=
  ⟨(S.mesh.location_mem_interval m i).1.le, (S.mesh.location_mem_interval m i).2.le⟩

theorem radius_div_eq_sqrt (r : ℝ) (hr : 0 < r) (i : S.Node) :
    S.radius r i / r = Real.sqrt (1 - (S.positionCoeff i)^2) := by
  simp [radius, positionCoeff, mul_div_cancel_left₀ _ (ne_of_gt hr)]

private theorem samplingEnd_sq_identity :
    (samplingEnd S.τ)^2 * (4 + S.τ^2) = 4 := by
  have hq : Real.sqrt (1 + S.τ^2 / 4) ≠ 0 := ne_of_gt (by positivity)
  have hs := Real.sq_sqrt (show 0 ≤ 1 + S.τ^2 / 4 by positivity)
  unfold samplingEnd
  field_simp
  rw [show 1 + S.τ^2 / 4 = (4 + S.τ^2) / 4 by ring] at hs
  nlinarith

theorem radius_lower (r : ℝ) (hr : 0 ≤ r) (i : S.Node) :
    r * S.R / Real.sqrt 5 ≤ S.radius r i := by
  have ht : 0 < S.τ := S.R_pos.trans_le S.R_le_τ
  have he : 0 ≤ samplingEnd S.τ := S.samplingEnd_pos.le
  have he1 : samplingEnd S.τ ≤ 1 := S.samplingEnd_lt_one.le
  have hi := S.positionCoeff_mem i
  have hi1 : S.positionCoeff i ≤ 1 := hi.2.trans he1
  have he2 : (samplingEnd S.τ)^2 ≤ 1 := by nlinarith
  have hit : (S.positionCoeff i)^2 ≤ (samplingEnd S.τ)^2 := by nlinarith
  have ht2 : S.τ^2 ≤ 1 := by nlinarith [S.τ_le_one]
  have hR2 : S.R^2 ≤ S.τ^2 := by nlinarith [S.R_pos, S.R_le_τ]
  have hmass := S.samplingEnd_sq_identity
  have hprod := mul_nonneg (sub_nonneg.mpr ht2) (sub_nonneg.mpr he2)
  have hrad : 0 ≤ 1 - (S.positionCoeff i)^2 := by nlinarith
  have hs := Real.sq_sqrt hrad
  have hspos := Real.sqrt_nonneg (1 - (S.positionCoeff i)^2)
  have hfive : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  have hfivepos : 0 < Real.sqrt 5 := by positivity
  have hquot : (S.R / Real.sqrt 5)^2 = S.R^2 / 5 := by
    field_simp
    nlinarith
  have hcore : S.R / Real.sqrt 5 ≤ Real.sqrt (1 - (S.positionCoeff i)^2) := by
    have hquotpos : 0 ≤ S.R / Real.sqrt 5 := div_nonneg S.R_pos.le hfivepos.le
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hcore hr
  simpa only [radius, positionCoeff, mul_div_assoc] using hmul

theorem shift_shape_le_one (r : ℝ) (hr : 0 < r) (i : S.Node) :
    |1 - S.positionCoeff i * samplingEnd S.τ| / (S.radius r i / r) ≤ 1 := by
  have hi := S.positionCoeff_mem i
  have he : 0 ≤ samplingEnd S.τ := S.samplingEnd_pos.le
  have he1 : samplingEnd S.τ ≤ 1 := S.samplingEnd_lt_one.le
  have hi1 : S.positionCoeff i ≤ 1 := hi.2.trans he1
  have hsq : 0 ≤ 1 - (S.positionCoeff i)^2 := by nlinarith
  have hs := Real.sq_sqrt hsq
  have hspos := Real.sqrt_nonneg (1 - (S.positionCoeff i)^2)
  have hmul : S.positionCoeff i * samplingEnd S.τ ≤ 1 :=
    (mul_le_mul_of_nonneg_left he1 hi.1).trans (by simpa using hi1)
  have hprod := mul_nonneg hi.1 (sub_nonneg.mpr hi.2)
  have hprod2 := mul_nonneg (sq_nonneg (S.positionCoeff i))
    (show 0 ≤ 1 - (samplingEnd S.τ)^2 by nlinarith)
  have hcore : |1 - S.positionCoeff i * samplingEnd S.τ| ≤
      Real.sqrt (1 - (S.positionCoeff i)^2) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hmul)]
    nlinarith
  rw [S.radius_div_eq_sqrt r hr i]
  exact (div_le_one (by
    simpa only [S.radius_div_eq_sqrt r hr i] using div_pos (S.radius_pos r hr i) hr)).mpr hcore

theorem shift_shape_le (r : ℝ) (hr : 0 < r) (i : S.Node) :
    |1 - S.positionCoeff i * samplingEnd S.τ| / (S.radius r i / r) ≤ 3 :=
  (S.shift_shape_le_one r hr i).trans (by norm_num)

end AcceleratedLogConcave.Numerics.AffineGraph.SamplingGeometry
end AffineBoundsShapes

noncomputable section AffineBoundsLipschitz
/-!
Finite affine Lipschitz bounds, with a difference-only L² adapter. Raw states
need only be AE strongly measurable, and only their differences need be L².
The common direct field cancels before membership is proved. No finiteness
assumption on the measure or moment assumption on the direct field is used.
-/


open MeasureTheory
open scoped BigOperators NNReal ContDiff

namespace AcceleratedLogConcave.Numerics.AffineGraph

section FiniteNorm

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A scalar row acts on a finite product with its absolute row mass. -/
theorem norm_sum_smul_le_of_norm_le (w : ι → ℝ) (v : ι → E) {A B : ℝ}
    (hw : ∑ j, |w j| ≤ A) (hB : 0 ≤ B) (hv : ∀ j, ‖v j‖ ≤ B) :
    ‖∑ j, w j • v j‖ ≤ A * B := by
  calc
    _ ≤ ∑ j, ‖w j • v j‖ := norm_sum_le _ _
    _ = ∑ j, |w j| * ‖v j‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ j, |w j| * B := by
      exact Finset.sum_le_sum (fun j _ ↦ mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _))
    _ = (∑ j, |w j|) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ A * B := mul_le_mul_of_nonneg_right hw hB

/-- The same anchor cancels before the Lipschitz estimate is applied. -/
theorem norm_weighted_reply_sub_le (w : ι → ℝ) (g : ι → E → E)
    (κ : ℝ≥0) {A : ℝ} (hw : ∑ j, |w j| ≤ A)
    (hg : ∀ j, LipschitzWith κ (g j)) (c : E) (X Y : ι → E) :
    ‖(c + ∑ j, w j • g j (X j)) - (c + ∑ j, w j • g j (Y j))‖ ≤
      (κ : ℝ) * A * ‖X - Y‖ := by
  have heq : (c + ∑ j, w j • g j (X j)) - (c + ∑ j, w j • g j (Y j)) =
      ∑ j, w j • (g j (X j) - g j (Y j)) := by
    simp only [smul_sub, Finset.sum_sub_distrib, add_sub_add_left_eq_sub]
  rw [heq]
  have hnorm : ∀ j, ‖g j (X j) - g j (Y j)‖ ≤ (κ : ℝ) * ‖X - Y‖ := by
    intro j
    exact ((hg j).norm_sub_le (X j) (Y j)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm (X - Y) j) κ.coe_nonneg)
  simpa only [mul_left_comm A (κ : ℝ), mul_assoc] using
    norm_sum_smul_le_of_norm_le w (fun j ↦ g j (X j) - g j (Y j)) hw
      (mul_nonneg κ.coe_nonneg (norm_nonneg _)) hnorm

namespace FiniteGraph

/-- The literal synchronous graph step, with an explicit scalar row estimate. -/
theorem norm_step_sub_le (G : FiniteGraph ι E) (u : E → ℝ → E)
    (κ : ℝ≥0) {A : ℝ} (hrow : ∀ i, ∑ j, |G.matrix i j| ≤ A)
    (hu : ∀ j, LipschitzWith κ (fun x ↦ u x (G.radius j)))
    (X Y : ι → E) (i : ι) :
    ‖G.step u X i - G.step u Y i‖ ≤ (κ : ℝ) * A * ‖X - Y‖ :=
  norm_weighted_reply_sub_le (G.matrix i) (fun j x ↦ u x (G.radius j))
    κ (hrow i) hu (G.direct i) X Y

end FiniteGraph
end FiniteNorm

section RawDifferences

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E]
variable {μ : Measure Ω} {κ : ℝ≥0} {g : E → E} {X Y : Ω → E}

/-- A Lipschitz reply difference is L² even when neither state is L². -/
theorem memLp_lipschitz_sub (hg : LipschitzWith κ g)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hD : MemLp (fun sample ↦ X sample - Y sample) 2 μ) :
    MemLp (fun sample ↦ g (X sample) - g (Y sample)) 2 μ := by
  apply hD.of_le_mul
    ((hg.continuous.comp_aestronglyMeasurable hX).sub
      (hg.continuous.comp_aestronglyMeasurable hY))
  exact Filter.Eventually.of_forall (fun sample ↦ hg.norm_sub_le (X sample) (Y sample))

/-- The Lipschitz factor is unchanged by taking the norm of the L² difference. -/
theorem norm_toLp_lipschitz_sub_le (hg : LipschitzWith κ g)
    (hD : MemLp (fun sample ↦ X sample - Y sample) 2 μ)
    (hH : MemLp (fun sample ↦ g (X sample) - g (Y sample)) 2 μ) :
    ‖hH.toLp (fun sample ↦ g (X sample) - g (Y sample))‖ ≤
      (κ : ℝ) * ‖hD.toLp (fun sample ↦ X sample - Y sample)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hH.coeFn_toLp, hD.coeFn_toLp] with sample hHsample hDsample
  simpa only [hHsample, hDsample] using hg.norm_sub_le (X sample) (Y sample)

variable [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

/-- Actual affine-output differences are L² after the arbitrary shared field
has canceled. No measurability or moment premise on that field is needed. -/
theorem memLp_weighted_reply_sub (w : ι → ℝ) (g : ι → E → E) (κ : ℝ≥0)
    (hg : ∀ j, LipschitzWith κ (g j)) (B : Ω → E) (X Y : ι → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample ↦ X j sample - Y j sample) 2 μ) :
    MemLp (fun sample ↦ (B sample + ∑ j, w j • g j (X j sample)) -
      (B sample + ∑ j, w j • g j (Y j sample))) 2 μ := by
  have hH (j : ι) := memLp_lipschitz_sub (hg j) (hX j) (hY j) (hD j)
  have hsum := memLp_finsetSum Finset.univ (fun j _ ↦ (hH j).const_smul (w j))
  apply hsum.ae_eq
  filter_upwards with sample
  simp only [Pi.smul_apply, smul_sub, Finset.sum_sub_distrib, add_sub_add_left_eq_sub]

/-- The maximum is outside the individual L² norms, on a finite product of
genuine Lp differences. The supplied membership witness is proved above. -/
theorem norm_toLp_weighted_reply_sub_le (w : ι → ℝ) (g : ι → E → E)
    (κ : ℝ≥0) {A : ℝ} (hw : ∑ j, |w j| ≤ A)
    (hg : ∀ j, LipschitzWith κ (g j)) (B : Ω → E) (X Y : ι → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample ↦ X j sample - Y j sample) 2 μ)
    (hS : MemLp (fun sample ↦ (B sample + ∑ j, w j • g j (X j sample)) -
      (B sample + ∑ j, w j • g j (Y j sample))) 2 μ) :
    ‖hS.toLp (fun sample ↦ (B sample + ∑ j, w j • g j (X j sample)) -
      (B sample + ∑ j, w j • g j (Y j sample)))‖ ≤
      (κ : ℝ) * A * ‖fun j ↦ (hD j).toLp (fun sample ↦ X j sample - Y j sample)‖ := by
  let hH (j : ι) := memLp_lipschitz_sub (hg j) (hX j) (hY j) (hD j)
  let H (j : ι) : Lp E 2 μ := (hH j).toLp (fun sample ↦ g j (X j sample) - g j (Y j sample))
  let D (j : ι) : Lp E 2 μ := (hD j).toLp (fun sample ↦ X j sample - Y j sample)
  have hsum : (∑ j, w j • H j : Lp E 2 μ) =ᵐ[μ]
      (fun sample ↦ ∑ j, w j • (g j (X j sample) - g j (Y j sample))) := by
    have hterm (j : ι) : (w j • H j : Lp E 2 μ) =ᵐ[μ]
        (fun sample ↦ w j • (g j (X j sample) - g j (Y j sample))) := by
      filter_upwards [Lp.coeFn_smul (w j) (H j), (hH j).coeFn_toLp] with sample hs ht
      change H j sample = _ at ht
      simp only [Pi.smul_apply, hs, ht]
    apply (Lp.coeFn_finsetSum Finset.univ (fun j ↦ w j • H j)).trans
    refine (eventuallyEq_sum (s := Finset.univ) (fun j _ ↦ hterm j)).trans ?_
    exact Filter.Eventually.of_forall (fun sample ↦ by simp only [Finset.sum_apply])
  have heq : hS.toLp (fun sample ↦ (B sample + ∑ j, w j • g j (X j sample)) -
      (B sample + ∑ j, w j • g j (Y j sample))) = ∑ j, w j • H j := by
    apply Lp.ext
    filter_upwards [hS.coeFn_toLp, hsum] with sample hs ht
    rw [hs, ht]
    simp only [smul_sub, Finset.sum_sub_distrib, add_sub_add_left_eq_sub]
  rw [heq]
  have hnorm : ∀ j, ‖H j‖ ≤ (κ : ℝ) * ‖D‖ := by
    intro j
    exact (norm_toLp_lipschitz_sub_le (hg j) (hD j) (hH j)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm D j) κ.coe_nonneg)
  simpa only [mul_left_comm A (κ : ℝ), mul_assoc] using
    norm_sum_smul_le_of_norm_le w H hw
      (mul_nonneg κ.coe_nonneg (norm_nonneg D)) hnorm

end RawDifferences

section Primitive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : E → ℝ} {L : ℝ}
variable (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
  (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
  (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)

include hF hL hlo hup

namespace FiniteGraph

/-- Generic primitive specialization; actual mean/sampling row bounds can be
substituted here without any graph contraction assumption. -/
theorem norm_step_primitiveMean_sub_le {ι : Type*} [Fintype ι]
    (G : FiniteGraph ι E) {A : ℝ} (hrow : ∀ i, ∑ j, |G.matrix i j| ≤ A)
    (hr : ∀ j, 0 < G.radius j) (X Y : ι → E) (i : ι) :
    ‖G.step (Gibbs.primitiveMean F) X i - G.step (Gibbs.primitiveMean F) Y i‖ ≤
      L * A * ‖X - Y‖ :=
  G.norm_step_sub_le (Gibbs.primitiveMean F) ⟨L, hL⟩ hrow
    (fun j ↦ Gibbs.primitive_mean_lipschitz hF hL hlo hup (hr j)) X Y i

end FiniteGraph

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem memLp_primitiveMean_sub {r : ℝ} (hr : 0 < r) {X Y : Ω → E}
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hD : MemLp (fun sample ↦ X sample - Y sample) 2 μ) :
    MemLp (fun sample ↦ Gibbs.primitiveMean F (X sample) r - Gibbs.primitiveMean F (Y sample) r) 2 μ :=
  memLp_lipschitz_sub (Gibbs.primitive_mean_lipschitz hF hL hlo hup hr) hX hY hD

theorem norm_toLp_primitiveMean_sub_le {r : ℝ} (hr : 0 < r) {X Y : Ω → E}
    (hD : MemLp (fun sample ↦ X sample - Y sample) 2 μ)
    (hH : MemLp (fun sample ↦ Gibbs.primitiveMean F (X sample) r -
      Gibbs.primitiveMean F (Y sample) r) 2 μ) :
    ‖hH.toLp (fun sample ↦ Gibbs.primitiveMean F (X sample) r - Gibbs.primitiveMean F (Y sample) r)‖ ≤
      L * ‖hD.toLp (fun sample ↦ X sample - Y sample)‖ :=
  norm_toLp_lipschitz_sub_le (Gibbs.primitive_mean_lipschitz hF hL hlo hup hr) hD hH

theorem memLp_weighted_primitiveMean_sub {ι : Type*} [Fintype ι]
    (w r : ι → ℝ) (hr : ∀ j, 0 < r j) (B : Ω → E) (X Y : ι → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample ↦ X j sample - Y j sample) 2 μ) :
    MemLp (fun sample ↦ (B sample + ∑ j, w j • Gibbs.primitiveMean F (X j sample) (r j)) -
      (B sample + ∑ j, w j • Gibbs.primitiveMean F (Y j sample) (r j))) 2 μ :=
  memLp_weighted_reply_sub w (fun j x ↦ Gibbs.primitiveMean F x (r j)) ⟨L, hL⟩
    (fun j ↦ Gibbs.primitive_mean_lipschitz hF hL hlo hup (hr j)) B X Y hX hY hD

theorem norm_toLp_weighted_primitiveMean_sub_le {ι : Type*} [Fintype ι]
    (w r : ι → ℝ) (hr : ∀ j, 0 < r j) {A : ℝ} (hw : ∑ j, |w j| ≤ A)
    (B : Ω → E) (X Y : ι → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample ↦ X j sample - Y j sample) 2 μ)
    (hS : MemLp (fun sample ↦ (B sample + ∑ j, w j • Gibbs.primitiveMean F (X j sample) (r j)) -
      (B sample + ∑ j, w j • Gibbs.primitiveMean F (Y j sample) (r j))) 2 μ) :
    ‖hS.toLp (fun sample ↦ (B sample + ∑ j, w j • Gibbs.primitiveMean F (X j sample) (r j)) -
      (B sample + ∑ j, w j • Gibbs.primitiveMean F (Y j sample) (r j)))‖ ≤
      L * A * ‖fun j ↦ (hD j).toLp (fun sample ↦ X j sample - Y j sample)‖ :=
  norm_toLp_weighted_reply_sub_le w (fun j x ↦ Gibbs.primitiveMean F x (r j))
    ⟨L, hL⟩ hw (fun j ↦ Gibbs.primitive_mean_lipschitz hF hL hlo hup (hr j))
    B X Y hX hY hD hS

end Primitive
end AcceleratedLogConcave.Numerics.AffineGraph
end AffineBoundsLipschitz

noncomputable section AffineBoundsSmallness
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineGraph

/-- The relaxed source parameter region leaves the explicit exponent gap `1/12`. -/
theorem affine_smallness_exponent_gap {b t w : ℝ}
    (hb : (1 : ℝ) / 2 ≤ b) (hwt : w ≤ t) (ht : t ≤ (1 : ℝ) / 60) :
    (1 : ℝ) / 12 ≤ b - 4 * t - w - (1 : ℝ) / 3 := by
  linarith

/-- Scalar envelope for the actual mean row bound. The graph's geometric caps remain
separate hypotheses of the graph theorem consuming this algebraic estimate. -/
theorem affine_mean_envelope_le {m : ℕ} (hm : 2 ≤ m)
    {δ b t w S L r σ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ w) (hwt : w ≤ t) (hS : 1 ≤ S) (hσ : 0 < σ)
    (hsizeR : L * r ^ 2 ≤ S * δ ^ b)
    (hsizeS : L * r / σ ≤ S * δ ^ b) :
    2 * L * (256 * (m : ℝ) ^ 5 * r /
        (σ * δ ^ (4 * t) * δ ^ w) + 4 * r ^ 2) ≤
      520 * (m : ℝ) ^ 5 * S * δ ^ (b - 4 * t - w) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hm)
  have hm5 : (1 : ℝ) ≤ (m : ℝ) ^ 5 := one_le_pow₀ hm1
  have hS0 : 0 ≤ S := by linarith
  have ht0 : 0 ≤ t := le_trans hw hwt
  have hp4 : 0 < δ ^ (4 * t) := Real.rpow_pos_of_pos hδ _
  have hpw : 0 < δ ^ w := Real.rpow_pos_of_pos hδ _
  have hpow : δ ^ b / (δ ^ (4 * t) * δ ^ w) =
      δ ^ (b - 4 * t - w) := by
    rw [Real.rpow_sub hδ, Real.rpow_sub hδ]
    ring
  have hb_le : δ ^ b ≤ δ ^ (b - 4 * t - w) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hfirst : 512 * (m : ℝ) ^ 5 * (L * r / σ) /
      (δ ^ (4 * t) * δ ^ w) ≤
      512 * (m : ℝ) ^ 5 * S * δ ^ (b - 4 * t - w) := by
    calc
      _ ≤ 512 * (m : ℝ) ^ 5 * (S * δ ^ b) /
          (δ ^ (4 * t) * δ ^ w) := by
        gcongr
      _ = 512 * (m : ℝ) ^ 5 * S * δ ^ (b - 4 * t - w) := by
        rw [← hpow]
        ring
  have hsecond : 8 * L * r ^ 2 ≤
      8 * (m : ℝ) ^ 5 * S * δ ^ (b - 4 * t - w) := by
    calc
      _ = 8 * (L * r ^ 2) := by ring
      _ ≤ 8 * (S * δ ^ b) := mul_le_mul_of_nonneg_left hsizeR (by norm_num)
      _ ≤ 8 * (S * δ ^ (b - 4 * t - w)) := by gcongr
      _ = 1 * (8 * S * δ ^ (b - 4 * t - w)) := by ring
      _ ≤ (m : ℝ) ^ 5 * (8 * S * δ ^ (b - 4 * t - w)) :=
        mul_le_mul_of_nonneg_right hm5 (by positivity)
      _ = _ := by ring
  calc
    _ = 512 * (m : ℝ) ^ 5 * (L * r / σ) /
        (δ ^ (4 * t) * δ ^ w) + 8 * L * r ^ 2 := by
      field_simp [hσ.ne', hp4.ne', hpw.ne']
      ring
    _ ≤ 512 * (m : ℝ) ^ 5 * S * δ ^ (b - 4 * t - w) +
        8 * (m : ℝ) ^ 5 * S * δ ^ (b - 4 * t - w) := add_le_add hfirst hsecond
    _ = _ := by ring

/-- The explicit resolution threshold pays the reciprocal twelfth power. -/
theorem rpow_resolution_mul_le_one {δ C : ℝ} (hδ : 0 < δ) (hC : 0 < C)
    (hres : δ ≤ C ^ (-12 : ℝ)) : C * δ ^ ((1 : ℝ) / 12) ≤ 1 := by
  have hroot := Real.rpow_le_rpow hδ.le hres (show 0 ≤ (1 : ℝ) / 12 by norm_num)
  have hexact : (C ^ (-12 : ℝ)) ^ ((1 : ℝ) / 12) = C⁻¹ := by
    rw [← Real.rpow_mul hC.le]
    norm_num [Real.rpow_neg_one]
  rw [hexact] at hroot
  calc
    _ ≤ C * C⁻¹ := mul_le_mul_of_nonneg_left hroot hC.le
    _ = 1 := mul_inv_cancel₀ hC.ne'

/-- The source exponent gap turns the explicit resolution threshold into the
required one-third power, without assuming a contraction conclusion. -/
theorem affine_resolution_envelope_le {δ C b t w : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 < C)
    (hb : (1 : ℝ) / 2 ≤ b) (hwt : w ≤ t) (ht : t ≤ (1 : ℝ) / 60)
    (hres : δ ≤ C ^ (-12 : ℝ)) :
    C * δ ^ (b - 4 * t - w) ≤ δ ^ ((1 : ℝ) / 3) := by
  have hgap := affine_smallness_exponent_gap hb hwt ht
  have hpow := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hgap
  have hcoef : C * δ ^ (b - 4 * t - w - (1 : ℝ) / 3) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow hC.le).trans
      (rpow_resolution_mul_le_one hδ hC hres)
  have he : b - 4 * t - w =
      (b - 4 * t - w - (1 : ℝ) / 3) + (1 : ℝ) / 3 := by ring
  calc
    _ = (C * δ ^ (b - 4 * t - w - (1 : ℝ) / 3)) * δ ^ ((1 : ℝ) / 3) := by
      conv_lhs => rw [he, Real.rpow_add hδ]
      ring
    _ ≤ 1 * δ ^ ((1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hδ.le _)
    _ = _ := one_mul _

/-- The actual mean-row envelope is small at the displayed sufficient resolution. -/
theorem affine_mean_envelope_le_rpow_third {m : ℕ} (hm : 2 ≤ m)
    {δ b t w S L r σ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ w) (hwt : w ≤ t) (ht : t ≤ (1 : ℝ) / 60)
    (hb : (1 : ℝ) / 2 ≤ b) (hS : 1 ≤ S) (hσ : 0 < σ)
    (hsizeR : L * r ^ 2 ≤ S * δ ^ b)
    (hsizeS : L * r / σ ≤ S * δ ^ b)
    (hres : δ ≤ (520 * (m : ℝ) ^ 5 * S) ^ (-12 : ℝ)) :
    2 * L * (256 * (m : ℝ) ^ 5 * r /
        (σ * δ ^ (4 * t) * δ ^ w) + 4 * r ^ 2) ≤ δ ^ ((1 : ℝ) / 3) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hS0 : 0 < S := by linarith
  exact (affine_mean_envelope_le hm hδ hδ1 hw hwt hS hσ hsizeR hsizeS).trans
    (affine_resolution_envelope_le hδ hδ1 (by positivity) hb hwt ht hres)

/-- The same numerical envelope pays the smaller sampling row estimate. -/
theorem affine_sampling_envelope_le {m : ℕ} (hm : 2 ≤ m)
    {δ b t w S L r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ w) (hwt : w ≤ t) (hS : 1 ≤ S)
    (hsizeR : L * r ^ 2 ≤ S * δ ^ b) :
    2 * L * r ^ 2 ≤ 520 * (m : ℝ) ^ 5 * S * δ ^ (b - 4 * t - w) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hm)
  have hm5 : (1 : ℝ) ≤ (m : ℝ) ^ 5 := one_le_pow₀ hm1
  have hS0 : 0 ≤ S := by linarith
  have ht0 : 0 ≤ t := le_trans hw hwt
  have hb_le : δ ^ b ≤ δ ^ (b - 4 * t - w) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  calc
    _ = 2 * (L * r ^ 2) := by ring
    _ ≤ 2 * (S * δ ^ b) := mul_le_mul_of_nonneg_left hsizeR (by norm_num)
    _ ≤ 2 * (S * δ ^ (b - 4 * t - w)) := by gcongr
    _ ≤ (520 * (m : ℝ) ^ 5) * (S * δ ^ (b - 4 * t - w)) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-- Sampling inherits the same sufficient resolution without an additional size bound. -/
theorem affine_sampling_envelope_le_rpow_third {m : ℕ} (hm : 2 ≤ m)
    {δ b t w S L r : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ w) (hwt : w ≤ t) (ht : t ≤ (1 : ℝ) / 60)
    (hb : (1 : ℝ) / 2 ≤ b) (hS : 1 ≤ S)
    (hsizeR : L * r ^ 2 ≤ S * δ ^ b)
    (hres : δ ≤ (520 * (m : ℝ) ^ 5 * S) ^ (-12 : ℝ)) :
    2 * L * r ^ 2 ≤ δ ^ ((1 : ℝ) / 3) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  have hS0 : 0 < S := by linarith
  exact (affine_sampling_envelope_le hm hδ hδ1 hw hwt hS hsizeR).trans
    (affine_resolution_envelope_le hδ hδ1 (by positivity) hb hwt ht hres)

end AcceleratedLogConcave.Numerics.AffineGraph
end AffineBoundsSmallness

noncomputable section AffineBoundsIteration
namespace AcceleratedLogConcave.Numerics.AffineGraph.FiniteGraph
variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- The actual prescribed synchronous iteration is the corresponding finite
function iterate, with its actual direct vector as initial state. -/
theorem iterate_eq_function_iterate (A : FiniteGraph ι E) (u : E → ℝ → E) (N : ℕ) :
    A.iterate u N = (A.step u)^[N] A.direct := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ← ih]
    rfl

end AcceleratedLogConcave.Numerics.AffineGraph.FiniteGraph
end AffineBoundsIteration

noncomputable section AffineBoundsActualSteps
/-!
Concrete primitive-mean step estimates for the actual mean and sampling graphs.
The mean graph uses the selected geometric backward partition, so its row mass
and first-cell estimate are proved rather than supplied. Raw comparisons use
arbitrary shared anchor fields and only L² membership of state differences.
-/


open MeasureTheory
open scoped BigOperators ContDiff

namespace AcceleratedLogConcave.Numerics.AffineGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : E → ℝ} {L : ℝ}
variable (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
  (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
  (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖ ^ 2)

include hF hL hlo hup

namespace SamplingGeometry

variable {m : ℕ} (S : SamplingGeometry m)

/-- Pointwise primitive Lipschitz supplier from the actual sampling rows. -/
theorem norm_step_primitiveMean_sub_le (hm : 0 < m) (r : ℝ) (hr : 0 < r)
    (x y0 : E) (X Y : S.Node → E) (i : S.Node) :
    ‖(S.graph r x y0).step (Gibbs.primitiveMean F) X i -
      (S.graph r x y0).step (Gibbs.primitiveMean F) Y i‖ ≤
      L * r ^ 2 * ‖X - Y‖ := by
  exact FiniteGraph.norm_step_primitiveMean_sub_le hF hL hlo hup
    (S.graph r x y0) (S.sum_abs_matrix_le hm r hr.le x y0)
    (S.radius_pos r hr) X Y i

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Actual sampling step differences are L², with no absolute-anchor moments. -/
theorem memLp_step_primitiveMean_sub (r : ℝ) (hr : 0 < r)
    (x y0 : Ω → E) (X Y : S.Node → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample ↦ X j sample - Y j sample) 2 μ)
    (i : S.Node) :
    MemLp (fun sample ↦
      (S.graph r (x sample) (y0 sample)).step (Gibbs.primitiveMean F)
        (fun j ↦ X j sample) i -
      (S.graph r (x sample) (y0 sample)).step (Gibbs.primitiveMean F)
        (fun j ↦ Y j sample) i) 2 μ := by
  exact memLp_weighted_primitiveMean_sub hF hL hlo hup
    ((S.graph r (0 : E) 0).matrix i) (S.radius r) (S.radius_pos r hr)
    (fun sample ↦ (S.graph r (x sample) (y0 sample)).direct i) X Y hX hY hD

/-- Membership and the actual sampling row bound are supplied together. The
finite-product norm is the maximum of the individual L² error norms. -/
theorem exists_memLp_step_primitiveMean_sub_le (hm : 0 < m) (r : ℝ) (hr : 0 < r)
    (x y0 : Ω → E) (X Y : S.Node → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample ↦ X j sample - Y j sample) 2 μ)
    (i : S.Node) :
    ∃ hS : MemLp (fun sample ↦
      (S.graph r (x sample) (y0 sample)).step (Gibbs.primitiveMean F)
        (fun j ↦ X j sample) i -
      (S.graph r (x sample) (y0 sample)).step (Gibbs.primitiveMean F)
        (fun j ↦ Y j sample) i) 2 μ,
      ‖hS.toLp (fun sample ↦
        (S.graph r (x sample) (y0 sample)).step (Gibbs.primitiveMean F)
          (fun j ↦ X j sample) i -
        (S.graph r (x sample) (y0 sample)).step (Gibbs.primitiveMean F)
          (fun j ↦ Y j sample) i)‖ ≤
        L * r ^ 2 * ‖fun j ↦ (hD j).toLp (fun sample ↦ X j sample - Y j sample)‖ := by
  let hS := S.memLp_step_primitiveMean_sub hF hL hlo hup r hr x y0 X Y hX hY hD i
  refine ⟨hS, ?_⟩
  exact norm_toLp_weighted_primitiveMean_sub_le hF hL hlo hup
    ((S.graph r (0 : E) 0).matrix i) (S.radius r) (S.radius_pos r hr)
    (S.sum_abs_matrix_le hm r hr.le (0 : E) 0 i)
    (fun sample ↦ (S.graph r (x sample) (y0 sample)).direct i) X Y hX hY hD hS

end SamplingGeometry

namespace MeanGeometry

variable {m : ℕ} (G : MeanGeometry m)

/-- The chosen backward partition supplies the first width and hence the
actual matrix estimate; neither estimate is an input to this theorem. -/
theorem norm_step_primitiveMean_sub_le_actualKernel (hm : 2 ≤ m)
    (r σ h₀ : ℝ) (hr : 0 < r) (hs : 0 < σ) (hpsi : G.psi ≤ 1)
    (hh : 0 < h₀) (hhupper : h₀ ≤ 1 / 2)
    (hback : G.backward = actualKernelInterval G.R h₀ G.R_pos G.R_le_half hh)
    (x y0 g0 : E) (ζ : Fin m → G.Kernel → E) (X Y : G.MeanNode → E)
    (i : G.MeanNode) :
    ‖(G.graph r σ x y0 g0 ζ).step (Gibbs.primitiveMean F) X i -
      (G.graph r σ x y0 g0 ζ).step (Gibbs.primitiveMean F) Y i‖ ≤
      L * (256 * (m : ℝ) ^ 5 * r / (σ * G.psi * h₀) + 4 * r ^ 2) * ‖X - Y‖ := by
  have hfirst : h₀ / 4 ≤ G.backward.length 0 := by
    rw [hback]
    exact actualKernelInterval_firstCell_lower G.R_pos G.R_le_half hh hhupper
  exact FiniteGraph.norm_step_primitiveMean_sub_le hF hL hlo hup
    (G.graph r σ x y0 g0 ζ)
    (G.sum_abs_matrix_le hm r σ hr.le hs hpsi h₀ hh hhupper hfirst)
    (G.radius_pos r hr) X Y i

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Shared position, score and seed fields cancel before L² membership is
proved; none of these fields needs a measurability or moment premise. -/
theorem memLp_step_primitiveMean_sub (r σ : ℝ) (hr : 0 < r)
    (x y0 g0 : Ω → E) (ζ : Ω → Fin m → G.Kernel → E)
    (X Y : G.MeanNode → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample ↦ X j sample - Y j sample) 2 μ)
    (i : G.MeanNode) :
    MemLp (fun sample ↦
      (G.graph r σ (x sample) (y0 sample) (g0 sample) (ζ sample)).step
        (Gibbs.primitiveMean F) (fun j ↦ X j sample) i -
      (G.graph r σ (x sample) (y0 sample) (g0 sample) (ζ sample)).step
        (Gibbs.primitiveMean F) (fun j ↦ Y j sample) i) 2 μ := by
  exact memLp_weighted_primitiveMean_sub hF hL hlo hup (G.matrix r σ i)
    (G.radius r) (G.radius_pos r hr)
    (fun sample ↦ G.direct r σ (x sample) (y0 sample) (g0 sample) (ζ sample) i)
    X Y hX hY hD

/-- The actual selected-mesh primitive step supplies its own L² membership and
the source row constant, with a maximum outside the individual L² norms. -/
theorem exists_memLp_step_primitiveMean_sub_le_actualKernel (hm : 2 ≤ m)
    (r σ h₀ : ℝ) (hr : 0 < r) (hs : 0 < σ) (hpsi : G.psi ≤ 1)
    (hh : 0 < h₀) (hhupper : h₀ ≤ 1 / 2)
    (hback : G.backward = actualKernelInterval G.R h₀ G.R_pos G.R_le_half hh)
    (x y0 g0 : Ω → E) (ζ : Ω → Fin m → G.Kernel → E)
    (X Y : G.MeanNode → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample ↦ X j sample - Y j sample) 2 μ)
    (i : G.MeanNode) :
    ∃ hS : MemLp (fun sample ↦
      (G.graph r σ (x sample) (y0 sample) (g0 sample) (ζ sample)).step
        (Gibbs.primitiveMean F) (fun j ↦ X j sample) i -
      (G.graph r σ (x sample) (y0 sample) (g0 sample) (ζ sample)).step
        (Gibbs.primitiveMean F) (fun j ↦ Y j sample) i) 2 μ,
      ‖hS.toLp (fun sample ↦
        (G.graph r σ (x sample) (y0 sample) (g0 sample) (ζ sample)).step
          (Gibbs.primitiveMean F) (fun j ↦ X j sample) i -
        (G.graph r σ (x sample) (y0 sample) (g0 sample) (ζ sample)).step
          (Gibbs.primitiveMean F) (fun j ↦ Y j sample) i)‖ ≤
        L * (256 * (m : ℝ) ^ 5 * r / (σ * G.psi * h₀) + 4 * r ^ 2) *
          ‖fun j ↦ (hD j).toLp (fun sample ↦ X j sample - Y j sample)‖ := by
  have hfirst : h₀ / 4 ≤ G.backward.length 0 := by
    rw [hback]
    exact actualKernelInterval_firstCell_lower G.R_pos G.R_le_half hh hhupper
  let hS := G.memLp_step_primitiveMean_sub hF hL hlo hup r σ hr
    x y0 g0 ζ X Y hX hY hD i
  refine ⟨hS, ?_⟩
  exact norm_toLp_weighted_primitiveMean_sub_le hF hL hlo hup (G.matrix r σ i)
    (G.radius r) (G.radius_pos r hr)
    (G.sum_abs_matrix_le hm r σ hr.le hs hpsi h₀ hh hhupper hfirst i)
    (fun sample ↦ G.direct r σ (x sample) (y0 sample) (g0 sample) (ζ sample) i)
    X Y hX hY hD hS

end MeanGeometry
end AcceleratedLogConcave.Numerics.AffineGraph
end AffineBoundsActualSteps

noncomputable section AffineBoundsOutputs
open MeasureTheory
open scoped BigOperators NNReal ContDiff

namespace AcceleratedLogConcave.Numerics.AffineGraph
open GaussLegendre

namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)

/-- The actual final row, extended by zero to the existing full node inventory. -/
def outputWeight : G.MeanNode → ℝ
  | .inl _ => 0
  | .inr (.inl b) => weight m b
  | .inr (.inr _) => 0

theorem sum_abs_outputWeight (hm : 0 < m) :
    (∑ j : G.MeanNode, |G.outputWeight j|) = 1 := by
  simpa only [MeanNode, Fintype.sum_sum_type, outputWeight, abs_zero,
    Finset.sum_const_zero, zero_add, add_zero] using sum_abs_meanOutput_weights hm

section Algebra
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem meanOutput_eq_weighted_sum (σ : ℝ) (g0 : E) (Q : G.MeanNode → E) :
    G.meanOutput σ g0 Q = (σ/2) • g0 + ∑ j, G.outputWeight j • Q j := by
  simp only [meanOutput, MeanNode, Fintype.sum_sum_type, outputWeight, zero_smul,
    Finset.sum_const_zero, zero_add, add_zero, MeanNode.center]
end Algebra

section Norm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_meanOutput_sub_le (hm : 0 < m) (σ : ℝ) (g0 : E)
    (X Y : G.MeanNode → E) :
    ‖G.meanOutput σ g0 X - G.meanOutput σ g0 Y‖ ≤ ‖X - Y‖ := by
  simpa only [G.meanOutput_eq_weighted_sum, NNReal.coe_one, one_mul] using
    norm_weighted_reply_sub_le G.outputWeight (fun _ x => x) 1
      (G.sum_abs_outputWeight hm).le (fun _ => LipschitzWith.id) ((σ/2) • g0) X Y
end Norm
end MeanGeometry

namespace SamplingGeometry
variable {m : ℕ} (S : SamplingGeometry m)

/-- The actual signed final probability integration row. -/
def outputWeight (r : ℝ) (j : S.Node) : ℝ :=
  -(r / samplingEnd S.τ) * S.row (samplingEnd S.τ) j

theorem sum_abs_outputWeight (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) :
    (∑ j : S.Node, |S.outputWeight r j|) = r :=
  S.sum_abs_output_weights hm r hr

section Algebra
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem output_eq_weighted_sum (r : ℝ) (y0 : E) (Q : S.Node → E) :
    S.output r y0 Q = (samplingEnd S.τ)⁻¹ • y0 + ∑ j, S.outputWeight r j • Q j := by
  simp only [output, outputWeight, mul_smul, neg_smul, Finset.sum_neg_distrib,
    ← Finset.smul_sum, sub_eq_add_neg]
end Algebra

section Norm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_output_sub_le (hm : 0 < m) (r : ℝ) (hr : 0 ≤ r) (y0 : E)
    (X Y : S.Node → E) : ‖S.output r y0 X - S.output r y0 Y‖ ≤ r * ‖X - Y‖ := by
  simpa only [S.output_eq_weighted_sum, NNReal.coe_one, one_mul] using
    norm_weighted_reply_sub_le (S.outputWeight r) (fun _ x => x) 1
      (S.sum_abs_outputWeight hm r hr).le (fun _ => LipschitzWith.id)
      ((samplingEnd S.τ)⁻¹ • y0) X Y
end Norm
end SamplingGeometry

section Primitive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : E → ℝ} {L : ℝ}
variable (hF : ContDiff ℝ 2 F) (hL : 0 ≤ L)
  (hlo : ∀ y v, 0 ≤ fderiv ℝ (fderiv ℝ F) y v v)
  (hup : ∀ y v, fderiv ℝ (fderiv ℝ F) y v v ≤ L * ‖v‖^2)
include hF hL hlo hup

namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)

theorem norm_meanOutput_collect_primitiveMean_sub_le (hm : 0 < m)
    (r : ℝ) (hr : 0 < r) (σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (X Y : G.MeanNode → E) :
    ‖G.meanOutput σ g0 ((G.graph r σ x y0 g0 ζ).collect (Gibbs.primitiveMean F) X) -
      G.meanOutput σ g0 ((G.graph r σ x y0 g0 ζ).collect (Gibbs.primitiveMean F) Y)‖ ≤
      L * ‖X - Y‖ := by
  convert
    norm_weighted_reply_sub_le G.outputWeight
      (fun j z => Gibbs.primitiveMean F z (G.radius r j)) (⟨L, hL⟩ : ℝ≥0)
      (G.sum_abs_outputWeight hm).le
      (fun j => Gibbs.primitive_mean_lipschitz hF hL hlo hup (G.radius_pos r hr j))
      ((σ/2) • g0) X Y using 1
  · simp only [G.meanOutput_eq_weighted_sum, FiniteGraph.collect, FiniteGraph.requests,
      graph]
  · change L * ‖X - Y‖ = L * 1 * ‖X - Y‖
    rw [mul_one]
end MeanGeometry

namespace SamplingGeometry
variable {m : ℕ} (S : SamplingGeometry m)

theorem norm_output_collect_primitiveMean_sub_le (hm : 0 < m)
    (r : ℝ) (hr : 0 < r) (x y0 : E) (X Y : S.Node → E) :
    ‖S.output r y0 ((S.graph r x y0).collect (Gibbs.primitiveMean F) X) -
      S.output r y0 ((S.graph r x y0).collect (Gibbs.primitiveMean F) Y)‖ ≤
      L * r * ‖X - Y‖ := by
  convert
    norm_weighted_reply_sub_le (S.outputWeight r)
      (fun j z => Gibbs.primitiveMean F z (S.radius r j)) (⟨L, hL⟩ : ℝ≥0)
      (S.sum_abs_outputWeight hm r hr.le).le
      (fun j => Gibbs.primitive_mean_lipschitz hF hL hlo hup (S.radius_pos r hr j))
      ((samplingEnd S.τ)⁻¹ • y0) X Y using 1
  · simp only [S.output_eq_weighted_sum, FiniteGraph.collect, FiniteGraph.requests,
      graph]
  · rfl
end SamplingGeometry

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)

/-- Only state differences require L² moments. The shared raw score field cancels. -/
theorem memLp_meanOutput_collect_primitiveMean_sub
    (r : ℝ) (hr : 0 < r) (σ : ℝ) (x y0 : E) (g0 : Ω → E)
    (ζ : Fin m → G.Kernel → E) (X Y : G.MeanNode → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample => X j sample - Y j sample) 2 μ) :
    MemLp (fun sample =>
      G.meanOutput σ (g0 sample) ((G.graph r σ x y0 (g0 sample) ζ).collect
        (Gibbs.primitiveMean F) (fun j => X j sample)) -
      G.meanOutput σ (g0 sample) ((G.graph r σ x y0 (g0 sample) ζ).collect
        (Gibbs.primitiveMean F) (fun j => Y j sample))) 2 μ := by
  simpa only [G.meanOutput_eq_weighted_sum, FiniteGraph.collect,
    FiniteGraph.requests, graph] using
    memLp_weighted_primitiveMean_sub hF hL hlo hup G.outputWeight (G.radius r)
      (G.radius_pos r hr) (fun sample => (σ/2) • g0 sample) X Y hX hY hD

/-- The finite-product L² norm is taken after each node's L² norm. -/
theorem norm_toLp_meanOutput_collect_primitiveMean_sub_le (hm : 0 < m)
    (r : ℝ) (hr : 0 < r) (σ : ℝ) (x y0 : E) (g0 : Ω → E)
    (ζ : Fin m → G.Kernel → E) (X Y : G.MeanNode → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample => X j sample - Y j sample) 2 μ) :
    ‖(G.memLp_meanOutput_collect_primitiveMean_sub hF hL hlo hup
      r hr σ x y0 g0 ζ X Y hX hY hD).toLp _‖ ≤
      L * ‖fun j => (hD j).toLp (fun sample => X j sample - Y j sample)‖ := by
  let hS := memLp_weighted_primitiveMean_sub hF hL hlo hup G.outputWeight (G.radius r)
    (G.radius_pos r hr) (fun sample => (σ/2) • g0 sample) X Y hX hY hD
  have hn := norm_toLp_weighted_primitiveMean_sub_le hF hL hlo hup
    G.outputWeight (G.radius r) (G.radius_pos r hr) (G.sum_abs_outputWeight hm).le
    (fun sample => (σ/2) • g0 sample) X Y hX hY hD hS
  simpa only [G.meanOutput_eq_weighted_sum, FiniteGraph.collect,
    FiniteGraph.requests, graph, mul_one] using hn
end MeanGeometry

namespace SamplingGeometry
variable {m : ℕ} (S : SamplingGeometry m)

/-- The raw initial-position field is shared and needs no moment assumption. -/
theorem memLp_output_collect_primitiveMean_sub
    (r : ℝ) (hr : 0 < r) (x : E) (y0 : Ω → E) (X Y : S.Node → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample => X j sample - Y j sample) 2 μ) :
    MemLp (fun sample =>
      S.output r (y0 sample) ((S.graph r x (y0 sample)).collect
        (Gibbs.primitiveMean F) (fun j => X j sample)) -
      S.output r (y0 sample) ((S.graph r x (y0 sample)).collect
        (Gibbs.primitiveMean F) (fun j => Y j sample))) 2 μ := by
  simpa only [S.output_eq_weighted_sum, FiniteGraph.collect,
    FiniteGraph.requests, graph] using
    memLp_weighted_primitiveMean_sub hF hL hlo hup (S.outputWeight r) (S.radius r)
      (S.radius_pos r hr) (fun sample => (samplingEnd S.τ)⁻¹ • y0 sample) X Y hX hY hD

theorem norm_toLp_output_collect_primitiveMean_sub_le (hm : 0 < m)
    (r : ℝ) (hr : 0 < r) (x : E) (y0 : Ω → E) (X Y : S.Node → Ω → E)
    (hX : ∀ j, AEStronglyMeasurable (X j) μ)
    (hY : ∀ j, AEStronglyMeasurable (Y j) μ)
    (hD : ∀ j, MemLp (fun sample => X j sample - Y j sample) 2 μ) :
    ‖(S.memLp_output_collect_primitiveMean_sub hF hL hlo hup
      r hr x y0 X Y hX hY hD).toLp _‖ ≤
      L * r * ‖fun j => (hD j).toLp (fun sample => X j sample - Y j sample)‖ := by
  let hS := memLp_weighted_primitiveMean_sub hF hL hlo hup (S.outputWeight r) (S.radius r)
    (S.radius_pos r hr) (fun sample => (samplingEnd S.τ)⁻¹ • y0 sample) X Y hX hY hD
  have hn := norm_toLp_weighted_primitiveMean_sub_le hF hL hlo hup
    (S.outputWeight r) (S.radius r) (S.radius_pos r hr) (S.sum_abs_outputWeight hm r hr.le).le
    (fun sample => (samplingEnd S.τ)⁻¹ • y0 sample) X Y hX hY hD hS
  simpa only [S.output_eq_weighted_sum, FiniteGraph.collect,
    FiniteGraph.requests, graph] using hn
end SamplingGeometry
end Primitive

end AcceleratedLogConcave.Numerics.AffineGraph
end AffineBoundsOutputs
