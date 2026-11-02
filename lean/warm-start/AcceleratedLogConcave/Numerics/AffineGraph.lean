import AcceleratedLogConcave.Numerics.ReciprocalQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Actual finite affine collocation graphs

The deterministic graph and finite synchronous mean-request inventory from
`warm-start.tex:2182–2259,2391–2424`. Quadrature coefficients are constructed
from the actual GL rules. No fixed-point solver, residual estimate, contraction,
Gaussian law, gradient compiler or work bound is assumed in this construction.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace AcceleratedLogConcave.Numerics.AffineGraph
open GaussLegendre ReciprocalQuadrature

/-- An actual finite strictly increasing partition, with both exact endpoints. -/
structure IntervalMesh (lo hi : ℝ) where
  cellsPred : ℕ
  point : Fin (cellsPred + 2) → ℝ
  strictMono : StrictMono point
  first : point 0 = lo
  last : point (Fin.last (cellsPred + 1)) = hi

namespace IntervalMesh
variable {lo hi : ℝ} (M : IntervalMesh lo hi)
abbrev Cell := Fin (M.cellsPred + 1)
abbrev Source (m : ℕ) := M.Cell × Fin m

def left (c : M.Cell) : ℝ := M.point c.castSucc
def right (c : M.Cell) : ℝ := M.point c.succ
def length (c : M.Cell) : ℝ := M.right c - M.left c

theorem length_pos (c : M.Cell) : 0 < M.length c :=
  sub_pos.mpr (M.strictMono c.castSucc_lt_succ)

theorem lo_le_left (c : M.Cell) : lo ≤ M.left c := by
  simpa only [M.first, left] using M.strictMono.monotone (Fin.zero_le c.castSucc)

theorem right_le_hi (c : M.Cell) : M.right c ≤ hi := by
  simpa only [M.last, right] using M.strictMono.monotone (Fin.le_last c.succ)

include M in
theorem lo_lt_hi : lo < hi := by
  simpa only [M.first, M.last] using
    M.strictMono (show (0 : Fin (M.cellsPred + 2)) < Fin.last (M.cellsPred + 1) by
      change (0 : ℕ) < M.cellsPred + 1; omega)

def location (m : ℕ) (z : M.Source m) : ℝ :=
  cellNode m (M.left z.1) (M.length z.1) z.2

theorem location_mem_cell (m : ℕ) (z : M.Source m) :
    M.location m z ∈ Set.Ioo (M.left z.1) (M.right z.1) := by
  simpa [location, length] using
    cellNode_mem_Ioo m (M.left z.1) (M.length z.1) (M.length_pos z.1) z.2

theorem location_mem_interval (m : ℕ) (z : M.Source m) :
    M.location m z ∈ Set.Ioo lo hi :=
  ⟨lt_of_le_of_lt (M.lo_le_left _) (M.location_mem_cell m z).1,
   lt_of_lt_of_le (M.location_mem_cell m z).2 (M.right_le_hi _)⟩

theorem location_lt_of_cell_lt (m : ℕ) {c d : M.Cell} (hcd : c < d)
    (i j : Fin m) : M.location m (c,i) < M.location m (d,j) := by
  have hmid : M.right c ≤ M.left d := M.strictMono.monotone (by
    change c.val + 1 ≤ d.val; exact hcd)
  exact lt_of_lt_of_le (M.location_mem_cell m (c,i)).2
    (hmid.trans (M.location_mem_cell m (d,j)).1.le)

theorem location_injective (m : ℕ) : Function.Injective (M.location m) := by
  rintro ⟨c,i⟩ ⟨d,j⟩ he
  have hcd : c = d := by
    rcases lt_trichotomy c d with h | h | h
    · exact False.elim ((ne_of_lt (M.location_lt_of_cell_lt m h i j)) he)
    · exact h
    · exact False.elim ((ne_of_lt (M.location_lt_of_cell_lt m h j i)) he.symm)
  subst d
  have hij := (cellNode_strictMono m _ _ (M.length_pos c)).injective he
  exact Prod.ext rfl hij

/-- Physical clamping, before conversion to normalized GL cell coordinates. -/
def clipped (t : ℝ) (c : M.Cell) : ℝ := max (M.left c) (min t (M.right c))

/-- Actual cumulative GL row from the partition's left endpoint to target `t`. -/
def cumulative (m : ℕ) (t : ℝ) (z : M.Source m) : ℝ :=
  partialRow m (M.left z.1) (M.length z.1) 0
    ((M.clipped t z.1 - M.left z.1) / M.length z.1) (fun _ => 1) z.2

/-- Signed row from physical source `u` to physical target `v`. -/
def row (m : ℕ) (u v : ℝ) (z : M.Source m) : ℝ :=
  M.cumulative m v z - M.cumulative m u z

theorem cumulative_eq_integral (m : ℕ) (t : ℝ) (z : M.Source m) :
    M.cumulative m t z = ∫ y in M.left z.1..M.clipped t z.1,
      (cardinal m z.2).eval ((y - M.left z.1) / M.length z.1) := by
  have he : M.left z.1 + M.length z.1 *
      ((M.clipped t z.1 - M.left z.1) / M.length z.1) = M.clipped t z.1 := by
    field_simp [ne_of_gt (M.length_pos z.1)]
    ring
  simp only [cumulative, partialRow, mul_zero, add_zero, one_mul, he]

@[simp] theorem cumulative_lo (m : ℕ) (z : M.Source m) :
    M.cumulative m lo z = 0 := by
  have hlo := M.lo_le_left z.1
  have he : M.clipped lo z.1 = M.left z.1 := by
    simp only [clipped, max_eq_left_iff]; exact (min_le_left _ _).trans hlo
  simp [cumulative, he]

theorem cumulative_hi (m : ℕ) (z : M.Source m) :
    M.cumulative m hi z = cellWeight m (M.length z.1) z.2 := by
  have he : M.clipped hi z.1 = M.right z.1 := by
    rw [clipped, min_eq_right (M.right_le_hi _), max_eq_right]
    exact le_of_lt (sub_pos.mp (M.length_pos _))
  rw [cumulative, he]
  change partialRow m _ _ 0 (M.length z.1 / M.length z.1) _ _ = _
  rw [div_self (ne_of_gt (M.length_pos _))]
  exact partialRow_full_one m _ _ (M.length_pos _) _

@[simp] theorem row_self (m : ℕ) (u : ℝ) (z : M.Source m) : M.row m u u z = 0 :=
  sub_self _
theorem row_reverse (m : ℕ) (u v : ℝ) (z : M.Source m) :
    M.row m v u z = -M.row m u v z := by simp [row]

theorem row_endpoints (m : ℕ) (z : M.Source m) :
    M.row m lo hi z = cellWeight m (M.length z.1) z.2 := by
  simp [row, cumulative_hi]

theorem row_back_endpoints (m : ℕ) (z : M.Source m) :
    M.row m hi lo z = -cellWeight m (M.length z.1) z.2 := by
  simp [row, cumulative_hi]

@[simp] theorem card_source (m : ℕ) :
    Fintype.card (M.Source m) = (M.cellsPred + 1) * m := by
  simp [Source, Cell]
end IntervalMesh

/-- Common physical interval endpoints. -/
def backwardEnd (R : ℝ) : ℝ := Real.sqrt (1 - R^2)
def conditionalEnd : ℝ := 1 / Real.sqrt 2

/-- Actual deterministic mesh data. Conditional and forward partitions are
allowed to vary with every kernel target, including its origin. -/
structure MeanGeometry (m : ℕ) where
  R : ℝ
  R_pos : 0 < R
  R_le_half : R ≤ 1/2
  psi : ℝ
  psi_pos : 0 < psi
  backward : IntervalMesh 0 (backwardEnd R)
  conditional : (ρ : Option (backward.Source m)) → IntervalMesh 0 conditionalEnd
  forward : (ρ : Option (backward.Source m)) →
    IntervalMesh (kernelValueLocation m backward.point ρ) (backwardEnd R)

namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)
abbrev Kernel := Option (G.backward.Source m)
def rho (ρ : G.Kernel) : ℝ := kernelValueLocation m G.backward.point ρ
def kernelCoeff (ρ : G.Kernel) : ℝ := kernelValueCoefficient m G.backward.point ρ
def variance (ρ : G.Kernel) : ℝ := 1 - (G.rho ρ)^2
def rotationScale (ρ : G.Kernel) : ℝ := Real.sqrt (G.variance ρ / (1 + (G.rho ρ)^2))
def centerNode (b : Fin m) : ℝ := cellNode m 0 1 b
def centerRow (a : ℝ) (b : Fin m) : ℝ := partialRow m 0 1 0 a (fun _ => 1) b
def angleNode (z : Fin m) : ℝ := cellNode m 0 G.psi z
def angleDerivative (z : Fin m) : ℝ := derivativeRow m 0 G.psi 0 z

def backRow (a : ℝ) : G.backward.Source m → ℝ :=
  G.backward.row m (backwardEnd G.R) a

def condRow (ρ : G.Kernel) (η : ℝ) : (G.conditional ρ).Source m → ℝ :=
  (G.conditional ρ).row m 0 η

def forwRow (ρ : G.Kernel) (a : ℝ) : (G.forward ρ).Source m → ℝ :=
  (G.forward ρ).row m (G.rho ρ) a

@[simp] theorem rho_origin : G.rho none = 0 := rfl
@[simp] theorem rho_some (z : G.backward.Source m) :
    G.rho (some z) = G.backward.location m z := rfl

theorem rho_injective : Function.Injective G.rho :=
  kernelValueLocation_injective m G.backward.point G.backward.strictMono G.backward.first

theorem backwardEnd_pos : 0 < backwardEnd G.R := G.backward.lo_lt_hi

theorem backwardEnd_lt_one : backwardEnd G.R < 1 := by
  apply (Real.sqrt_lt' (by norm_num : (0:ℝ) < 1)).2
  nlinarith [sq_pos_of_pos G.R_pos]

theorem rho_mem (ρ : G.Kernel) : 0 ≤ G.rho ρ ∧ G.rho ρ < backwardEnd G.R := by
  cases ρ with
  | none => exact ⟨le_rfl, G.backwardEnd_pos⟩
  | some z => exact ⟨(G.backward.location_mem_interval m z).1.le,
      (G.backward.location_mem_interval m z).2⟩

theorem variance_pos (ρ : G.Kernel) : 0 < G.variance ρ := by
  have h := G.rho_mem ρ
  have h1 := h.2.trans G.backwardEnd_lt_one
  unfold variance
  nlinarith

theorem rotationScale_pos (ρ : G.Kernel) : 0 < G.rotationScale ρ :=
  Real.sqrt_pos.2 (div_pos (G.variance_pos ρ) (by positivity))

theorem rotationScale_sq (ρ : G.Kernel) :
    (G.rotationScale ρ)^2 = G.variance ρ / (1 + (G.rho ρ)^2) :=
  Real.sq_sqrt (div_nonneg (G.variance_pos ρ).le (by positivity))

/-- Occurrence-indexed inventory. Equal numerical data never identify slots. -/
abbrev MeanNode := Unit ⊕ Fin m ⊕ (Fin m × G.backward.Source m) ⊕
  (Fin m × (Σ ρ : G.Kernel, (G.conditional ρ).Source m)) ⊕
  (Fin m × (Σ ρ : G.Kernel, Fin m × (G.forward ρ).Source m))

namespace MeanNode
def base : G.MeanNode := .inl ()
def center (b : Fin m) : G.MeanNode := .inr (.inl b)
def backward (b : Fin m) (j : G.backward.Source m) : G.MeanNode :=
  .inr (.inr (.inl (b,j)))
def conditional (b : Fin m) (ρ : G.Kernel) (j : (G.conditional ρ).Source m) : G.MeanNode :=
  .inr (.inr (.inr (.inl (b,⟨ρ,j⟩))))
def forward (b : Fin m) (ρ : G.Kernel) (z : Fin m)
    (j : (G.forward ρ).Source m) : G.MeanNode :=
  .inr (.inr (.inr (.inr (b,⟨ρ,z,j⟩))))

theorem center_injective : Function.Injective (center G) := by
  intro b c h; simpa [center] using h
end MeanNode

theorem card_meanNode :
    Fintype.card G.MeanNode = 1 + m + m * Fintype.card (G.backward.Source m) +
      m * (∑ ρ : G.Kernel, Fintype.card ((G.conditional ρ).Source m)) +
      m * m * (∑ ρ : G.Kernel, Fintype.card ((G.forward ρ).Source m)) := by
  simp only [MeanNode, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
    Fintype.card_prod, Fintype.card_sigma, ← Finset.mul_sum]
  ring

theorem card_meanNode_le (P : ℕ) (hB : Fintype.card (G.backward.Source m) ≤ P)
    (hK : Fintype.card G.Kernel ≤ P)
    (hC : ∀ ρ, Fintype.card ((G.conditional ρ).Source m) ≤ P)
    (hF : ∀ ρ, Fintype.card ((G.forward ρ).Source m) ≤ P) :
    Fintype.card G.MeanNode ≤ 1 + m + m*P + m*P^2 + m^2*P^2 := by
  have hcs : (∑ ρ : G.Kernel, Fintype.card ((G.conditional ρ).Source m)) ≤ P*P := by
    calc
      _ ≤ ∑ _ : G.Kernel, P := Finset.sum_le_sum (fun ρ _ => hC ρ)
      _ = Fintype.card G.Kernel * P := by simp
      _ ≤ P * P := Nat.mul_le_mul_right P hK
  have hfs : (∑ ρ : G.Kernel, Fintype.card ((G.forward ρ).Source m)) ≤ P*P := by
    calc
      _ ≤ ∑ _ : G.Kernel, P := Finset.sum_le_sum (fun ρ _ => hF ρ)
      _ = Fintype.card G.Kernel * P := by simp
      _ ≤ P * P := Nat.mul_le_mul_right P hK
  rw [G.card_meanNode]
  calc
    _ ≤ 1 + m + m*P + m*(P*P) + m*m*(P*P) := by gcongr
    _ = _ := by ring

/-- Anchor slots: position, score, and every conditional auxiliary vector. -/
abbrev Anchor := Unit ⊕ Unit ⊕ (Fin m × G.Kernel)
abbrev Atom := G.Anchor ⊕ G.MeanNode
end MeanGeometry

/-- A finite scalar linear form, before any vector values are supplied. -/
abbrev Form (ι : Type*) := ι → ℝ
namespace Form
variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
def atom (i : ι) : Form ι := by
  classical
  exact fun j => if j = i then 1 else 0
def eval (a : Form ι) (v : ι → E) : E := ∑ i, a i • v i
@[simp] theorem eval_atom (i : ι) (v : ι → E) : eval (atom i) v = v i := by
  classical
  simp [eval, atom]
@[simp] theorem eval_zero (v : ι → E) : eval (0 : Form ι) v = 0 := by simp [eval]
@[simp] theorem eval_add (a b : Form ι) (v : ι → E) :
    eval (a+b) v = eval a v + eval b v := by simp [eval, add_smul, Finset.sum_add_distrib]
@[simp] theorem eval_sub (a b : Form ι) (v : ι → E) :
    eval (a-b) v = eval a v - eval b v := by simp [eval, sub_smul, Finset.sum_sub_distrib]
@[simp] theorem eval_smul (c : ℝ) (a : Form ι) (v : ι → E) :
    eval (c • a) v = c • eval a v := by simp [eval, smul_smul, Finset.smul_sum]
@[simp] theorem eval_sum {κ : Type*} (s : Finset κ) (a : κ → Form ι) (v : ι → E) :
    eval (∑ j ∈ s, a j) v = ∑ j ∈ s, eval (a j) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s h ih => simp [Finset.sum_insert h, ih]

/-- Matrix extraction is a theorem of finite linear-form evaluation. -/
theorem eval_split {α β : Type*} [Fintype α] [Fintype β]
    (a : Form (α ⊕ β)) (v : α → E) (q : β → E) :
    eval a (Sum.elim v q) =
      (∑ i, a (.inl i) • v i) + ∑ j, a (.inr j) • q j := by
  simp [eval, Fintype.sum_sum_type]
end Form

namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)

/-- Position and score anchors and conditional seeds are separate occurrences. -/
def positionAtom : G.Atom := .inl (.inl ())
def scoreAtom : G.Atom := .inl (.inr (.inl ()))
def seedAtom (b : Fin m) (ρ : G.Kernel) : G.Atom := .inl (.inr (.inr (b,ρ)))
def meanAtom (i : G.MeanNode) : G.Atom := .inr i

/-- The V-first elimination uses stored mean values directly. -/
def velocityForm (σ : ℝ) (b : Fin m) : Form G.Atom :=
  (σ/2)⁻¹ • ∑ ρ : G.Kernel, G.kernelCoeff ρ • ∑ z : Fin m,
    G.angleDerivative z • ∑ j : (G.forward ρ).Source m,
      G.forwRow ρ (backwardEnd G.R) j • Form.atom (G.meanAtom (.forward G b ρ z j))

def positionForm (σ a : ℝ) : Form G.Atom :=
  Form.atom G.positionAtom + ∑ b : Fin m,
    centerRow a b • G.velocityForm σ b

def scoreForm (σ a : ℝ) : Form G.Atom :=
  Form.atom G.scoreAtom + (σ/2)⁻¹ • ∑ b : Fin m, centerRow a b •
    (Form.atom (G.meanAtom (.center G b)) - Form.atom (G.meanAtom (.base G)))

def backwardForm (r σ : ℝ) (b : Fin m) (a : ℝ) : Form G.Atom :=
  G.positionForm σ (centerNode b) - r • ∑ j : G.backward.Source m,
    G.backRow a j • Form.atom (G.meanAtom (.backward G b j))

def conditionalForm (r : ℝ) (b : Fin m) (ρ : G.Kernel) (η : ℝ) : Form G.Atom :=
  Form.atom (G.seedAtom b ρ) - (r * Real.sqrt (G.variance ρ)) •
    ∑ j : (G.conditional ρ).Source m,
      G.condRow ρ η j • Form.atom (G.meanAtom (.conditional G b ρ j))

def observationForm (r σ : ℝ) (b : Fin m) (ρ : G.Kernel) : Form G.Atom :=
  G.rho ρ • G.backwardForm r σ b (G.rho ρ) +
    (Real.sqrt (G.variance ρ) / conditionalEnd) • G.conditionalForm r b ρ conditionalEnd

def midpointForm (r σ : ℝ) (b : Fin m) (ρ : G.Kernel) : Form G.Atom :=
  (G.rho ρ / (1 + (G.rho ρ)^2)) •
    (G.observationForm r σ b ρ + G.rho ρ • G.backwardForm r σ b (G.rho ρ))

def rotationForm (r σ : ℝ) (b : Fin m) (ρ : G.Kernel) (z : ℝ) : Form G.Atom :=
  G.midpointForm r σ b ρ + Real.cos (z / G.rotationScale ρ) •
    (G.backwardForm r σ b (G.rho ρ) - G.midpointForm r σ b ρ) +
    (G.rotationScale ρ * Real.sin (z / G.rotationScale ρ)) •
      G.scoreForm σ (centerNode b)

def forwardForm (r σ : ℝ) (b : Fin m) (ρ : G.Kernel) (z : Fin m) (a : ℝ) : Form G.Atom :=
  G.rotationForm r σ b ρ (G.angleNode z) - r • ∑ j : (G.forward ρ).Source m,
    G.forwRow ρ a j • Form.atom (G.meanAtom (.forward G b ρ z j))

/-- Center forms contain the outer physical scale as well as every inner correction. -/
def centerForm (r σ : ℝ) : G.MeanNode → Form G.Atom
  | .inl _ => 0
  | .inr (.inl b) => (r * backwardEnd G.R) • G.positionForm σ (centerNode b)
  | .inr (.inr (.inl (b,j))) => (r * G.backward.location m j) •
      G.backwardForm r σ b (G.backward.location m j)
  | .inr (.inr (.inr (.inl (b,⟨ρ,j⟩)))) =>
      (r * G.rho ρ) • G.backwardForm r σ b (G.rho ρ) +
      (r * Real.sqrt (G.variance ρ) * (G.conditional ρ).location m j) •
        G.conditionalForm r b ρ ((G.conditional ρ).location m j)
  | .inr (.inr (.inr (.inr (b,⟨ρ,z,j⟩)))) =>
      (r * (G.forward ρ).location m j) •
        G.forwardForm r σ b ρ z ((G.forward ρ).location m j)

def radius (r : ℝ) : G.MeanNode → ℝ
  | .inl _ => r
  | .inr (.inl _) => r * G.R
  | .inr (.inr (.inl (_,j))) => r * Real.sqrt (1 - (G.backward.location m j)^2)
  | .inr (.inr (.inr (.inl (_,⟨ρ,j⟩)))) =>
      r * Real.sqrt (G.variance ρ) * Real.sqrt (1 - ((G.conditional ρ).location m j)^2)
  | .inr (.inr (.inr (.inr (_,⟨ρ,_,j⟩)))) =>
      r * Real.sqrt (1 - ((G.forward ρ).location m j)^2)

section Vector
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def anchorValues (y0 g0 : E) (ζ : Fin m → G.Kernel → E) : G.Anchor → E
  | .inl _ => y0
  | .inr (.inl _) => g0
  | .inr (.inr (b,ρ)) => ζ b ρ

def values (y0 g0 : E) (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E) : G.Atom → E :=
  Sum.elim (G.anchorValues y0 g0 ζ) Q

/-- Actual free states, evaluated at one shared stored mean array. -/
def velocity (σ : ℝ) (Q : G.MeanNode → E) (b : Fin m) : E :=
  (σ/2)⁻¹ • ∑ ρ : G.Kernel, G.kernelCoeff ρ • ∑ z : Fin m,
    G.angleDerivative z • ∑ j : (G.forward ρ).Source m,
      G.forwRow ρ (backwardEnd G.R) j • Q (.forward G b ρ z j)

def position (σ : ℝ) (y0 : E) (Q : G.MeanNode → E) (a : ℝ) : E :=
  y0 + ∑ b : Fin m, centerRow a b • G.velocity σ Q b

def score (σ : ℝ) (g0 : E) (Q : G.MeanNode → E) (a : ℝ) : E :=
  g0 + (σ/2)⁻¹ • ∑ b : Fin m, centerRow a b • (Q (.center G b) - Q (.base G))

def backwardState (r σ : ℝ) (y0 : E) (Q : G.MeanNode → E) (b : Fin m) (a : ℝ) : E :=
  G.position σ y0 Q (centerNode b) - r • ∑ j : G.backward.Source m,
    G.backRow a j • Q (.backward G b j)

def conditionalState (r : ℝ) (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E)
    (b : Fin m) (ρ : G.Kernel) (η : ℝ) : E :=
  ζ b ρ - (r * Real.sqrt (G.variance ρ)) • ∑ j : (G.conditional ρ).Source m,
    G.condRow ρ η j • Q (.conditional G b ρ j)

def observation (r σ : ℝ) (y0 : E) (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E)
    (b : Fin m) (ρ : G.Kernel) : E :=
  G.rho ρ • G.backwardState r σ y0 Q b (G.rho ρ) +
    (Real.sqrt (G.variance ρ) / conditionalEnd) • G.conditionalState r ζ Q b ρ conditionalEnd

def midpoint (r σ : ℝ) (y0 : E) (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E)
    (b : Fin m) (ρ : G.Kernel) : E :=
  (G.rho ρ / (1 + (G.rho ρ)^2)) •
    (G.observation r σ y0 ζ Q b ρ + G.rho ρ • G.backwardState r σ y0 Q b (G.rho ρ))

def rotation (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E)
    (b : Fin m) (ρ : G.Kernel) (z : ℝ) : E :=
  G.midpoint r σ y0 ζ Q b ρ + Real.cos (z / G.rotationScale ρ) •
    (G.backwardState r σ y0 Q b (G.rho ρ) - G.midpoint r σ y0 ζ Q b ρ) +
    (G.rotationScale ρ * Real.sin (z / G.rotationScale ρ)) •
      G.score σ g0 Q (centerNode b)

def forwardState (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E)
    (b : Fin m) (ρ : G.Kernel) (z : Fin m) (a : ℝ) : E :=
  G.rotation r σ y0 g0 ζ Q b ρ (G.angleNode z) - r •
    ∑ j : (G.forward ρ).Source m, G.forwRow ρ a j • Q (.forward G b ρ z j)

/-- Literal free-state elimination, independent of the coefficient representation. -/
def centers (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) : G.MeanNode → E
  | .inl _ => x
  | .inr (.inl b) => x + (r * backwardEnd G.R) • G.position σ y0 Q (centerNode b)
  | .inr (.inr (.inl (b,j))) => x + (r * G.backward.location m j) •
      G.backwardState r σ y0 Q b (G.backward.location m j)
  | .inr (.inr (.inr (.inl (b,⟨ρ,j⟩)))) =>
      x + (r * G.rho ρ) • G.backwardState r σ y0 Q b (G.rho ρ) +
      (r * Real.sqrt (G.variance ρ) * (G.conditional ρ).location m j) •
        G.conditionalState r ζ Q b ρ ((G.conditional ρ).location m j)
  | .inr (.inr (.inr (.inr (b,⟨ρ,z,j⟩)))) =>
      x + (r * (G.forward ρ).location m j) •
        G.forwardState r σ y0 g0 ζ Q b ρ z ((G.forward ρ).location m j)

@[simp] theorem eval_velocityForm (σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) :
    Form.eval (G.velocityForm σ b) (G.values y0 g0 ζ Q) = G.velocity σ Q b := by
  simp [velocityForm, velocity, values, meanAtom]

@[simp] theorem eval_positionForm (σ a : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) :
    Form.eval (G.positionForm σ a) (G.values y0 g0 ζ Q) = G.position σ y0 Q a := by
  simp [positionForm, position, values, positionAtom, anchorValues, velocityForm, velocity, meanAtom]

@[simp] theorem eval_scoreForm (σ a : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) :
    Form.eval (G.scoreForm σ a) (G.values y0 g0 ζ Q) = G.score σ g0 Q a := by
  simp [scoreForm, score, values, scoreAtom, anchorValues, meanAtom]

@[simp] theorem eval_backwardForm (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) (a : ℝ) :
    Form.eval (G.backwardForm r σ b a) (G.values y0 g0 ζ Q) = G.backwardState r σ y0 Q b a := by
  rw [backwardForm, Form.eval_sub, G.eval_positionForm]
  simp only [Form.eval_smul, Form.eval_sum, Form.eval_atom, values, meanAtom,
    Sum.elim_inr, backwardState]

@[simp] theorem eval_conditionalForm (r : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) (ρ : G.Kernel) (η : ℝ) :
    Form.eval (G.conditionalForm r b ρ η) (G.values y0 g0 ζ Q) =
      G.conditionalState r ζ Q b ρ η := by
  simp [conditionalForm, conditionalState, values, seedAtom, anchorValues, meanAtom]

@[simp] theorem eval_observationForm (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) (ρ : G.Kernel) :
    Form.eval (G.observationForm r σ b ρ) (G.values y0 g0 ζ Q) =
      G.observation r σ y0 ζ Q b ρ := by simp [observationForm, observation]

@[simp] theorem eval_midpointForm (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) (ρ : G.Kernel) :
    Form.eval (G.midpointForm r σ b ρ) (G.values y0 g0 ζ Q) =
      G.midpoint r σ y0 ζ Q b ρ := by simp [midpointForm, midpoint]

@[simp] theorem eval_rotationForm (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) (ρ : G.Kernel) (z : ℝ) :
    Form.eval (G.rotationForm r σ b ρ z) (G.values y0 g0 ζ Q) =
      G.rotation r σ y0 g0 ζ Q b ρ z := by simp [rotationForm, rotation]

@[simp] theorem eval_forwardForm (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) (ρ : G.Kernel) (z : Fin m) (a : ℝ) :
    Form.eval (G.forwardForm r σ b ρ z a) (G.values y0 g0 ζ Q) =
      G.forwardState r σ y0 g0 ζ Q b ρ z a := by
  rw [forwardForm, Form.eval_sub, G.eval_rotationForm]
  simp only [Form.eval_smul, Form.eval_sum, Form.eval_atom, values, meanAtom,
    Sum.elim_inr, forwardState]

theorem centers_eq_form (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (i : G.MeanNode) :
    G.centers r σ x y0 g0 ζ Q i = x + Form.eval (G.centerForm r σ i) (G.values y0 g0 ζ Q) := by
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩ <;>
    simp [centers, centerForm, add_assoc]

/-- Actual mean coefficients, extracted from the constructed free-state forms. -/
def matrix (r σ : ℝ) (i j : G.MeanNode) : ℝ := G.centerForm r σ i (.inr j)

def direct (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E) (i : G.MeanNode) : E :=
  x + ∑ a : G.Anchor, G.centerForm r σ i (.inl a) • G.anchorValues y0 g0 ζ a

/-- The source affine system is derived, with no supplied matrix certificate. -/
theorem centers_eq_direct_add_matrix (r σ : ℝ) (x y0 g0 : E)
    (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E) (i : G.MeanNode) :
    G.centers r σ x y0 g0 ζ Q i = G.direct r σ x y0 g0 ζ i +
      ∑ j, G.matrix r σ i j • Q j := by
  rw [G.centers_eq_form, values, Form.eval_split]
  simp only [direct, matrix, add_assoc]

theorem direct_eq_centers_zero (r σ : ℝ) (x y0 g0 : E)
    (ζ : Fin m → G.Kernel → E) (i : G.MeanNode) :
    G.direct r σ x y0 g0 ζ i = G.centers r σ x y0 g0 ζ (fun _ => 0) i := by
  simp [G.centers_eq_direct_add_matrix]

@[simp] theorem rotation_zero (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) (ρ : G.Kernel) :
    G.rotation r σ y0 g0 ζ Q b ρ 0 = G.backwardState r σ y0 Q b (G.rho ρ) := by
  simp [rotation]

/-- The literal final mean row has exactly the centering occurrence slots. -/
def meanOutput (σ : ℝ) (g0 : E) (Q : G.MeanNode → E) : E :=
  (σ/2) • g0 + ∑ b : Fin m, weight m b • Q (.center G b)

@[simp] theorem center_radius (r : ℝ) (b : Fin m) : G.radius r (.center G b) = r*G.R := rfl
end Vector
end MeanGeometry

theorem conditionalEnd_pos : 0 < conditionalEnd := by unfold conditionalEnd; positivity

theorem conditionalEnd_lt_one : conditionalEnd < 1 := by
  have h : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  exact (div_lt_one (by positivity : 0 < Real.sqrt 2)).2 h

private theorem sqrt_one_sub_sq_pos {a : ℝ} (ha : 0 ≤ a) (h1 : a < 1) :
    0 < Real.sqrt (1-a^2) := by
  apply Real.sqrt_pos.2
  nlinarith

namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)

theorem radius_pos (r : ℝ) (hr : 0 < r) (i : G.MeanNode) : 0 < G.radius r i := by
  rcases i with _ | b | ⟨b,j⟩ | ⟨b,ρ,j⟩ | ⟨b,ρ,z,j⟩
  · exact hr
  · exact mul_pos hr G.R_pos
  · have h := G.backward.location_mem_interval m j
    exact mul_pos hr (sqrt_one_sub_sq_pos h.1.le (h.2.trans G.backwardEnd_lt_one))
  · have h := (G.conditional ρ).location_mem_interval m j
    exact mul_pos (mul_pos hr (Real.sqrt_pos.2 (G.variance_pos ρ)))
      (sqrt_one_sub_sq_pos h.1.le (h.2.trans conditionalEnd_lt_one))
  · have h := (G.forward ρ).location_mem_interval m j
    exact mul_pos hr (sqrt_one_sub_sq_pos ((G.rho_mem ρ).1.trans h.1.le)
      (h.2.trans G.backwardEnd_lt_one))

section Vector
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

@[simp] theorem velocity_zero (σ : ℝ) (b : Fin m) :
    G.velocity σ (fun _ => (0:E)) b = 0 := by simp [velocity]
@[simp] theorem position_zero (σ : ℝ) (y0 : E) (a : ℝ) :
    G.position σ y0 (fun _ => 0) a = y0 := by simp [position]
@[simp] theorem score_zero (σ : ℝ) (g0 : E) (a : ℝ) :
    G.score σ g0 (fun _ => 0) a = g0 := by simp [score]
@[simp] theorem backwardState_zero (r σ : ℝ) (y0 : E) (b : Fin m) (a : ℝ) :
    G.backwardState r σ y0 (fun _ => 0) b a = y0 := by simp [backwardState]
@[simp] theorem conditionalState_zero (r : ℝ) (ζ : Fin m → G.Kernel → E)
    (b : Fin m) (ρ : G.Kernel) (η : ℝ) :
    G.conditionalState r ζ (fun _ => 0) b ρ η = ζ b ρ := by simp [conditionalState]

/-- Exact direct-vector rotation coefficients, with the source q and eta. -/
theorem rotation_zero_values (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (b : Fin m) (ρ : G.Kernel) (z : ℝ) :
    G.rotation r σ y0 g0 ζ (fun _ => 0) b ρ z =
      (1 - (G.rotationScale ρ)^2 * (1 - Real.cos (z / G.rotationScale ρ))) • y0 +
      (G.rotationScale ρ * Real.sin (z / G.rotationScale ρ)) • g0 +
      (G.rho ρ * Real.sqrt (2 * G.variance ρ) *
        (1 - Real.cos (z / G.rotationScale ρ)) / (1 + (G.rho ρ)^2)) • ζ b ρ := by
  have hs : Real.sqrt (G.variance ρ) / conditionalEnd = Real.sqrt (2 * G.variance ρ) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp [conditionalEnd, mul_comm]
  simp only [rotation, midpoint, observation, backwardState_zero, conditionalState_zero, score_zero]
  rw [hs, G.rotationScale_sq]
  unfold variance
  match_scalars <;> field_simp <;> ring

@[simp] theorem direct_base (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E) :
    G.direct r σ x y0 g0 ζ (.base G) = x := by
  rw [G.direct_eq_centers_zero]; rfl

theorem direct_center (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E) (b : Fin m) :
    G.direct r σ x y0 g0 ζ (.center G b) = x + (r * backwardEnd G.R) • y0 := by
  rw [G.direct_eq_centers_zero]; simp [centers, MeanNode.center]

theorem direct_backward (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (b : Fin m) (j : G.backward.Source m) :
    G.direct r σ x y0 g0 ζ (.backward G b j) =
      x + (r * G.backward.location m j) • y0 := by
  rw [G.direct_eq_centers_zero]; simp [centers, MeanNode.backward]

theorem direct_conditional (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (b : Fin m) (ρ : G.Kernel) (j : (G.conditional ρ).Source m) :
    G.direct r σ x y0 g0 ζ (.conditional G b ρ j) = x + r •
      (G.rho ρ • y0 + (Real.sqrt (G.variance ρ) * (G.conditional ρ).location m j) • ζ b ρ) := by
  rw [G.direct_eq_centers_zero]
  simp only [centers, MeanNode.conditional, backwardState_zero, conditionalState_zero]
  module

theorem direct_forward (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (b : Fin m) (ρ : G.Kernel) (z : Fin m) (j : (G.forward ρ).Source m) :
    G.direct r σ x y0 g0 ζ (.forward G b ρ z j) =
      x + (r * (G.forward ρ).location m j) •
       ((1 - (G.rotationScale ρ)^2 * (1 - Real.cos (G.angleNode z / G.rotationScale ρ))) • y0 +
        (G.rotationScale ρ * Real.sin (G.angleNode z / G.rotationScale ρ)) • g0 +
        (G.rho ρ * Real.sqrt (2 * G.variance ρ) *
          (1 - Real.cos (G.angleNode z / G.rotationScale ρ)) / (1 + (G.rho ρ)^2)) • ζ b ρ) := by
  rw [G.direct_eq_centers_zero]
  simp [centers, MeanNode.forward, forwardState, G.rotation_zero_values]
end Vector
end MeanGeometry

/-- The actual physical information in one abstract mean-supplier request. -/
structure MeanRequest (E : Type*) where
  center : E
  radius : ℝ

/-- A finite affine system. Instances below are extracted from the literal
mean and sampling free states, rather than supplied as correctness premises. -/
structure FiniteGraph (ι E : Type*) where
  direct : ι → E
  matrix : ι → ι → ℝ
  radius : ι → ℝ

namespace FiniteGraph
variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
variable (A : FiniteGraph ι E)

def updateFromReplies (Q : ι → E) (i : ι) : E := A.direct i + ∑ j, A.matrix i j • Q j

def requests (old : ι → E) (i : ι) : MeanRequest E := ⟨old i, A.radius i⟩

/-- Collect the entire reply array at the old centers before updating any row. -/
def collect (u : E → ℝ → E) (old : ι → E) (i : ι) : E :=
  u (A.requests old i).center (A.requests old i).radius

def step (u : E → ℝ → E) (old : ι → E) : ι → E :=
  A.updateFromReplies (A.collect u old)

/-- Prescribed finite iteration; no fixed point or adaptive stopping is used. -/
def iterate (u : E → ℝ → E) (k : ℕ) : ι → E :=
  Nat.rec A.direct (fun _ old => A.step u old) k

@[simp] theorem iterate_zero (u : E → ℝ → E) : A.iterate u 0 = A.direct := rfl
@[simp] theorem iterate_succ (u : E → ℝ → E) (k : ℕ) :
    A.iterate u (k+1) = A.updateFromReplies (A.collect u (A.iterate u k)) := rfl
omit [Fintype ι] [AddCommGroup E] [Module ℝ E] in
@[simp] theorem request_center (old : ι → E) (i : ι) : (A.requests old i).center = old i := rfl
omit [Fintype ι] [AddCommGroup E] [Module ℝ E] in
@[simp] theorem request_radius (old : ι → E) (i : ι) :
    (A.requests old i).radius = A.radius i := rfl

theorem step_eq (u : E → ℝ → E) (old : ι → E) (i : ι) :
    A.step u old i = A.direct i + ∑ j, A.matrix i j • u (old j) (A.radius j) := rfl

/-- A fixed occurrence enumeration, independent of vector values and replies. -/
def enumeration (ι : Type*) [Fintype ι] : List ι := List.ofFn (Fintype.equivFin ι).symm

@[simp] theorem enumeration_length : (enumeration ι).length = Fintype.card ι := by
  simp [enumeration]

theorem enumeration_nodup : (enumeration ι).Nodup :=
  List.nodup_ofFn.mpr (Fintype.equivFin ι).symm.injective

theorem mem_enumeration (i : ι) : i ∈ enumeration ι := by
  exact List.mem_ofFn.mpr ⟨(Fintype.equivFin ι) i, (Fintype.equivFin ι).symm_apply_apply i⟩

/-- Requests retain their occurrence labels even when their data coincide. -/
def requestPlan (old : ι → E) : List (ι × MeanRequest E) :=
  (enumeration ι).map (fun i => (i, A.requests old i))

omit [AddCommGroup E] [Module ℝ E] in
@[simp] theorem requestPlan_length (old : ι → E) :
    (A.requestPlan old).length = Fintype.card ι := by simp [requestPlan]

omit [AddCommGroup E] [Module ℝ E] in
theorem requestPlan_labels (old : ι → E) :
    (A.requestPlan old).map Prod.fst = enumeration ι := by simp [requestPlan, List.map_map, Function.comp_def]

omit [AddCommGroup E] [Module ℝ E] in
theorem requestPlan_labels_nodup (old : ι → E) :
    ((A.requestPlan old).map Prod.fst).Nodup := by
  rw [A.requestPlan_labels]; exact enumeration_nodup

/-- The request inventory of exactly k complete synchronous layers. -/
def requestTrace (u : E → ℝ → E) (k : ℕ) : List (ι × MeanRequest E) :=
  Nat.rec [] (fun k acc => acc ++ A.requestPlan (A.iterate u k)) k

theorem requestTrace_length (u : E → ℝ → E) (k : ℕ) :
    (A.requestTrace u k).length = k * Fintype.card ι := by
  induction k with
  | zero => simp [requestTrace]
  | succ k ih =>
    change (A.requestTrace u k ++ A.requestPlan (A.iterate u k)).length = _
    rw [List.length_append, ih, A.requestPlan_length, Nat.succ_mul]
end FiniteGraph

namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The finite affine mean graph, extracted from the source free-state construction. -/
def graph (r σ : ℝ) (x y0 g0 : E) (ζ : Fin m → G.Kernel → E) :
    FiniteGraph G.MeanNode E :=
  ⟨G.direct r σ x y0 g0 ζ, G.matrix r σ, G.radius r⟩

theorem graph_update_eq_centers (r σ : ℝ) (x y0 g0 : E)
    (ζ : Fin m → G.Kernel → E) (Q : G.MeanNode → E) :
    (G.graph r σ x y0 g0 ζ).updateFromReplies Q = G.centers r σ x y0 g0 ζ Q := by
  funext i
  exact (G.centers_eq_direct_add_matrix r σ x y0 g0 ζ Q i).symm

theorem graph_step_eq_centers (r σ : ℝ) (x y0 g0 : E)
    (ζ : Fin m → G.Kernel → E) (u : E → ℝ → E) (old : G.MeanNode → E) :
    (G.graph r σ x y0 g0 ζ).step u old =
      G.centers r σ x y0 g0 ζ (fun i => u (old i) (G.radius r i)) :=
  G.graph_update_eq_centers r σ x y0 g0 ζ _

/-- The output's child list contains exactly m distinct centering slots. -/
def finalChildren : List G.MeanNode := List.ofFn (MeanNode.center G)
@[simp] theorem finalChildren_length : G.finalChildren.length = m := by simp [finalChildren]
theorem finalChildren_nodup : G.finalChildren.Nodup :=
  List.nodup_ofFn.mpr (MeanNode.center_injective G)
end MeanGeometry

/-- Sampling's physical terminal probability parameter. -/
def samplingEnd (τ : ℝ) : ℝ := (Real.sqrt (1 + τ^2/4))⁻¹

structure SamplingGeometry (m : ℕ) where
  R : ℝ
  R_pos : 0 < R
  R_le_half : R ≤ 1/2
  τ : ℝ
  R_le_τ : R ≤ τ
  τ_le_one : τ ≤ 1
  mesh : IntervalMesh 0 (samplingEnd τ)

namespace SamplingGeometry
variable {m : ℕ} (S : SamplingGeometry m)
abbrev Node := S.mesh.Source m

def row (a : ℝ) : S.Node → ℝ := S.mesh.row m 0 a

theorem samplingEnd_pos : 0 < samplingEnd S.τ := by unfold samplingEnd; positivity

theorem samplingEnd_lt_one : samplingEnd S.τ < 1 := by
  have ht : 0 < S.τ := S.R_pos.trans_le S.R_le_τ
  have h : 1 < Real.sqrt (1 + S.τ^2/4) :=
    (Real.lt_sqrt (by norm_num)).2 (by nlinarith [sq_pos_of_pos ht])
  exact inv_lt_one_of_one_lt₀ h

def radius (r : ℝ) (j : S.Node) : ℝ := r * Real.sqrt (1 - (S.mesh.location m j)^2)

theorem radius_pos (r : ℝ) (hr : 0 < r) (j : S.Node) : 0 < S.radius r j :=
  mul_pos hr (sqrt_one_sub_sq_pos (S.mesh.location_mem_interval m j).1.le
    ((S.mesh.location_mem_interval m j).2.trans S.samplingEnd_lt_one))

section Vector
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def state (r : ℝ) (y0 : E) (Q : S.Node → E) (a : ℝ) : E :=
  y0 - r • ∑ j, S.row a j • Q j

def centers (r : ℝ) (x y0 : E) (Q : S.Node → E) (i : S.Node) : E :=
  x + (r * S.mesh.location m i) • S.state r y0 Q (S.mesh.location m i)

def graph (r : ℝ) (x y0 : E) : FiniteGraph S.Node E where
  direct i := x + (r * S.mesh.location m i) • y0
  matrix i j := -(r * S.mesh.location m i) * r * S.row (S.mesh.location m i) j
  radius := S.radius r

theorem graph_update_eq_centers (r : ℝ) (x y0 : E) (Q : S.Node → E) :
    (S.graph r x y0).updateFromReplies Q = S.centers r x y0 Q := by
  funext i
  simp [FiniteGraph.updateFromReplies, graph, centers, state, sub_eq_add_neg,
    smul_add, smul_smul, Finset.smul_sum, Finset.sum_neg_distrib, mul_assoc, add_assoc]

def output (r : ℝ) (y0 : E) (Q : S.Node → E) : E :=
  (samplingEnd S.τ)⁻¹ • y0 - (r / samplingEnd S.τ) • ∑ j, S.row (samplingEnd S.τ) j • Q j

theorem output_eq_scaled_terminal (r : ℝ) (y0 : E) (Q : S.Node → E) :
    S.output r y0 Q = (samplingEnd S.τ)⁻¹ • S.state r y0 Q (samplingEnd S.τ) := by
  simp only [output, state, smul_sub, smul_smul, div_eq_mul_inv]
  congr 2
  ring

theorem output_eq_full_weights (r : ℝ) (y0 : E) (Q : S.Node → E) :
    S.output r y0 Q = (samplingEnd S.τ)⁻¹ • y0 - (r / samplingEnd S.τ) •
      ∑ j : S.Node, cellWeight m (S.mesh.length j.1) j.2 • Q j := by
  simp only [output, row, S.mesh.row_endpoints]
end Vector
end SamplingGeometry

namespace MeanGeometry
variable {m : ℕ} (G : MeanGeometry m)

theorem kernelCoeff_origin_neg : G.kernelCoeff none < 0 := by
  have hmass : 0 ≤ ∑ z : G.backward.Source m, kernelNodeCoefficient m G.backward.point z := by
    apply Finset.sum_nonneg
    intro z _
    apply div_nonneg
    · exact cellWeight_nonneg m _ _ (G.backward.length_pos z.1).le
    · exact sq_nonneg _
  change -1 / meshHorizon G.backward.point - _ < 0
  have he : meshHorizon G.backward.point = backwardEnd G.R := G.backward.last
  rw [he]
  have hp : 0 < 1 / backwardEnd G.R := one_div_pos.mpr G.backwardEnd_pos
  rw [neg_div]
  linarith

section Vector
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

@[simp] theorem position_source (σ : ℝ) (y0 : E) (Q : G.MeanNode → E) :
    G.position σ y0 Q 0 = y0 := by simp [position, centerRow]
@[simp] theorem score_source (σ : ℝ) (g0 : E) (Q : G.MeanNode → E) :
    G.score σ g0 Q 0 = g0 := by simp [score, centerRow]
@[simp] theorem backwardState_source (r σ : ℝ) (y0 : E) (Q : G.MeanNode → E) (b : Fin m) :
    G.backwardState r σ y0 Q b (backwardEnd G.R) = G.position σ y0 Q (centerNode b) := by
  simp [backwardState, backRow]
@[simp] theorem conditionalState_source (r : ℝ) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) (ρ : G.Kernel) :
    G.conditionalState r ζ Q b ρ 0 = ζ b ρ := by simp [conditionalState, condRow]
@[simp] theorem forwardState_source (r σ : ℝ) (y0 g0 : E) (ζ : Fin m → G.Kernel → E)
    (Q : G.MeanNode → E) (b : Fin m) (ρ : G.Kernel) (z : Fin m) :
    G.forwardState r σ y0 g0 ζ Q b ρ z (G.rho ρ) =
      G.rotation r σ y0 g0 ζ Q b ρ (G.angleNode z) := by simp [forwardState, forwRow]
end Vector
end MeanGeometry

end AcceleratedLogConcave.Numerics.AffineGraph
