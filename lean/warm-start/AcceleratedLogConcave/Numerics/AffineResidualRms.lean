import AcceleratedLogConcave.Numerics.AffineResidual
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# AffineResidualRms

Centered sampling residuals and deterministic iteration in Lp. Raw sampling
anchors need no absolute moments. The mean receiver uses the explicitly stronger
PrimitiveLpCorrespondence for absolute primitive outputs in Lp; it does not
construct that correspondence, analytic flows, or stationary regularity.
-/

noncomputable section AffineResidualRmsRmsDefs
open MeasureTheory Set
open scoped BigOperators ContDiff NNReal
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph

namespace AcceleratedLogConcave.Numerics.AffineResidual

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {μ : Measure Ω} {m : ℕ}

/-- An exact centered integral equation and local Banach regularity. No graph
residual, quadrature error, matrix bound, or absolute-state moment is a field. -/
structure SamplingLpReference (μ : Measure Ω) (S : SamplingGeometry m)
    (r : ℝ) (u : E → ℝ → E) (x y0 : Ω → E) where
  baseline : Ω → E
  path : ℝ → Ω → E
  curve : ℝ → Lp E 2 μ
  reply : ∀ a ∈ Icc (0 : ℝ) (samplingEnd S.τ),
    (fun sample => u (x sample + (r * a) • path a sample) (r * Real.sqrt (1 - a ^ 2)) -
      baseline sample) =ᵐ[μ] (curve a : Ω → E)
  flow : ∀ a ∈ Icc (0 : ℝ) (samplingEnd S.τ),
    path a =ᵐ[μ] (fun sample => y0 sample - r •
      (a • baseline sample + ((∫ t in (0 : ℝ)..a, curve t) : Lp E 2 μ) sample))
  cellBound : S.mesh.Cell → ℝ
  cellBound_nonneg : ∀ c, 0 ≤ cellBound c
  smooth : ∀ c, ∀ t ∈ Icc (S.mesh.left c) (S.mesh.right c),
    ContDiffAt ℝ m curve t
  deriv_bound : ∀ c, ∀ t ∈ Icc (S.mesh.left c) (S.mesh.right c),
    ‖iteratedDeriv m curve t‖ ≤ cellBound c

namespace SamplingLpReference

variable {S : SamplingGeometry m} {r : ℝ} {u : E → ℝ → E} {x y0 : Ω → E}
variable (P : SamplingLpReference μ S r u x y0)

def reference : S.Node → Ω → E :=
  fun i sample => x sample + (r * S.mesh.location m i) • P.path (S.mesh.location m i) sample

def rawResidual : S.Node → Ω → E := fun i sample =>
  (S.graph r (x sample) (y0 sample)).step u (fun j => P.reference j sample) i - P.reference i sample

def lpDefect (i : S.Node) : Lp E 2 μ :=
  (r ^ 2 * S.mesh.location m i) •
    ((∫ t in (0 : ℝ)..S.mesh.location m i, P.curve t) -
      ∑ j : S.Node, S.row (S.mesh.location m i) j • P.curve (S.mesh.location m j))

def cellBudget : ℝ :=
  ∑ c : S.mesh.Cell,
    2 * (S.mesh.length c) ^ (m + 1) * P.cellBound c / (m.factorial : ℝ)

/-- Proposed exact type, not a theorem. The residual equality is a conclusion
to derive from the actual row and exact flow equations, never an assumption. -/
def residualIdentityTarget : Prop :=
  1 ≤ m → ∀ i, P.rawResidual i =ᵐ[μ] (P.lpDefect i : Ω → E)

/-- Proposed full RMS type, not a theorem. The target supplies its own actual
raw-residual membership witnesses and takes the node maximum after L2. -/
def residualBoundTarget : Prop :=
  1 ≤ m → 0 < r →
    ∃ hres : ∀ i, MemLp (P.rawResidual i) 2 μ,
      Collocation.rawNodeErrorNorm μ P.rawResidual hres ≤
        r ^ 2 * samplingEnd S.τ * P.cellBudget

def rawIterationError (k : ℕ) : S.Node → Ω → E := fun i sample =>
  (S.graph r (x sample) (y0 sample)).iterate u k i - P.reference i sample

/-- Optional downstream deterministic-iteration consumer. The only state
moment assumption is initial difference membership. Coordinate measurability
of the combined direct array suffices; no separate anchor moments are needed. -/
def iterateBoundTarget (κ : ℝ≥0) : Prop :=
  1 ≤ m → 0 < r →
  (∀ j, LipschitzWith κ (fun z => u z (S.radius r j))) →
  (∀ i, AEStronglyMeasurable
    (fun sample => (S.graph r (x sample) (y0 sample)).direct i) μ) →
  (∀ i, AEStronglyMeasurable (P.reference i) μ) →
  (∀ i, MemLp (P.rawIterationError 0 i) 2 μ) →
  ∃ herr : ∀ k i, MemLp (P.rawIterationError k i) 2 μ,
    ∀ N, Collocation.rawNodeErrorNorm μ (P.rawIterationError N) (herr N) ≤
      ((κ : ℝ) * r ^ 2) ^ N *
        Collocation.rawNodeErrorNorm μ (P.rawIterationError 0) (herr 0) +
      (r ^ 2 * samplingEnd S.τ * P.cellBudget) *
        ∑ j ∈ Finset.range N, ((κ : ℝ) * r ^ 2) ^ j

end SamplingLpReference

end AcceleratedLogConcave.Numerics.AffineResidual

open MeasureTheory Set
open scoped BigOperators ContDiff
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineResidual.MeanRms

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {μ : Measure Ω} {m : ℕ}

def rawReference (G : MeanGeometry m) (x : Ω → E) (r : ℝ)
    (C : Mean.Curves G (Lp E 2 μ)) : G.MeanNode → Ω → E :=
  fun i sample => x sample + (C.reference G (0 : Lp E 2 μ) r i) sample

def rawResidual (G : MeanGeometry m) (u : E → ℝ → E) (x : Ω → E)
    (r σ : ℝ) (y0 g0 : Lp E 2 μ) (ζ : Fin m → G.Kernel → Lp E 2 μ)
    (C : Mean.Curves G (Lp E 2 μ)) : G.MeanNode → Ω → E := fun i sample =>
  (G.graph r σ (x sample) (y0 sample) (g0 sample) (fun b ρ => ζ b ρ sample)).step u
    (fun j => rawReference G x r C j sample) i - rawReference G x r C i sample

/-- This is a genuine integrable primitive-output lift, stronger than a
centered difference lift. Existence is an explicit upstream obligation. -/
def PrimitiveLpCorrespondence (u : E → ℝ → E) (x : Ω → E)
    (uLp : Lp E 2 μ → ℝ → Lp E 2 μ) : Prop :=
  ∀ (Z : Lp E 2 μ) (q : ℝ), 0 < q →
    (uLp Z q : Ω → E) =ᵐ[μ] (fun sample => u (x sample + Z sample) q)

/-- Proposed mean raw RMS receiver. It retains the exact actual graph and
returns residual membership. No residual identity/bound is an input. -/
def ResidualStatement (G : MeanGeometry m) : Prop :=
  2 ≤ m → ∀ (r σ h₀ l v : ℝ), 0 < r → 0 < σ → 0 ≤ h₀ →
    l < 0 → backwardEnd G.R < v →
    (∀ c, G.backward.length c ≤ 2*h₀*(1-(G.backward.right c)^2)) →
  ∀ (u : E → ℝ → E) (x : Ω → E)
    (uLp : Lp E 2 μ → ℝ → Lp E 2 μ)
    (y0 g0 : Lp E 2 μ) (ζ : Fin m → G.Kernel → Lp E 2 μ)
    (C : Mean.Curves G (Lp E 2 μ)) (D : Mean.DerivativeBudget G),
    PrimitiveLpCorrespondence u x uLp →
    Mean.Equations G C uLp r σ 0 y0 g0 ζ →
    Mean.Regularity G C uLp 0 r l v D →
    ∃ hres : ∀ i, MemLp (rawResidual G u x r σ y0 g0 ζ C i) 2 μ,
      ∀ i, ‖(hres i).toLp (rawResidual G u x r σ y0 g0 ζ C i)‖ ≤
        D.rowError G r σ h₀ i

end AcceleratedLogConcave.Numerics.AffineResidual.MeanRms
end AffineResidualRmsRmsDefs

noncomputable section AffineResidualRmsRmsHelpers
open MeasureTheory Set
open scoped BigOperators ContDiff NNReal
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph

namespace AcceleratedLogConcave.Numerics.AffineResidual

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure Ω}

/-- Evaluation commutes almost everywhere with a finite scalar combination. -/
theorem coeFn_weighted_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (v : ι → Lp E 2 μ) :
    (∑ i, w i • v i : Lp E 2 μ) =ᵐ[μ]
      (fun sample => ∑ i, w i • v i sample) := by
  apply (Lp.coeFn_finsetSum Finset.univ (fun i => w i • v i)).trans
  have ht (i : ι) : (w i • v i : Lp E 2 μ) =ᵐ[μ]
      (fun sample => w i • v i sample) := Lp.coeFn_smul (w i) (v i)
  exact (eventuallyEq_sum (s := Finset.univ) (fun i _ => ht i)).trans
    (Filter.Eventually.of_forall (fun sample => by simp only [Finset.sum_apply]))

omit [NormedSpace ℝ E] in
/-- The canonical Lp representative of an AE-equal raw field is the original Lp value. -/
theorem toLp_eq_of_ae {f : Ω → E} {v : Lp E 2 μ}
    (hf : MemLp f 2 μ) (he : f =ᵐ[μ] (v : Ω → E)) : hf.toLp f = v := by
  exact Lp.ext (hf.coeFn_toLp.trans he)

/-- Generic deterministic finite-graph iteration for raw states. Only differences
are L2; the direct field is assumed measurable, never integrable. -/
theorem raw_affine_iterate_bound {ι : Type*} [Fintype ι]
    (B : ι → Ω → E) (w : ι → ι → ℝ) (radius : ι → ℝ)
    (u : E → ℝ → E) (reference : ι → Ω → E)
    (κ : ℝ≥0) (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, |w i j| ≤ A)
    (hu : ∀ j, LipschitzWith κ (fun z => u z (radius j)))
    (hB : ∀ i, AEStronglyMeasurable (B i) μ)
    (href : ∀ i, AEStronglyMeasurable (reference i) μ)
    (hinit : ∀ i, MemLp (fun sample => B i sample - reference i sample) 2 μ)
    (hres : ∀ i, MemLp (fun sample => B i sample +
      ∑ j, w i j • u (reference j sample) (radius j) - reference i sample) 2 μ)
    (hresBound : ∀ i, ‖(hres i).toLp (fun sample => B i sample +
      ∑ j, w i j • u (reference j sample) (radius j) - reference i sample)‖ ≤ R) :
    let graph : Ω → FiniteGraph ι E := fun sample =>
      ⟨fun i => B i sample, w, radius⟩
    let err : ℕ → ι → Ω → E := fun k i sample =>
      (graph sample).iterate u k i - reference i sample
    ∃ herr : ∀ k i, MemLp (err k i) 2 μ,
      ∀ N, Collocation.rawNodeErrorNorm μ (err N) (herr N) ≤
        ((κ : ℝ) * A)^N * Collocation.rawNodeErrorNorm μ (err 0) (herr 0) +
          R * ∑ j ∈ Finset.range N, ((κ : ℝ) * A)^j := by
  classical
  dsimp only
  let graph : Ω → FiniteGraph ι E := fun sample => ⟨fun i => B i sample, w, radius⟩
  let X (k : ℕ) (i : ι) (sample : Ω) := (graph sample).iterate u k i
  let err (k : ℕ) (i : ι) (sample : Ω) := X k i sample - reference i sample
  have hX : ∀ k i, AEStronglyMeasurable (X k i) μ := by
    intro k
    induction k with
    | zero => exact hB
    | succ k ih =>
      intro i
      change AEStronglyMeasurable (fun sample => B i sample +
        ∑ j, w i j • u (X k j sample) (radius j)) μ
      apply (hB i).add
      convert Finset.aestronglyMeasurable_sum Finset.univ
          (fun j _ => ((hu j).continuous.comp_aestronglyMeasurable (ih j)).const_smul (w i j)) using 1
      ext sample
      simp only [Finset.sum_apply, Pi.smul_apply]
  have hdiff (k : ℕ) (hk : ∀ j, MemLp (err k j) 2 μ) (i : ι) :
      MemLp (fun sample => (graph sample).step u (fun j => X k j sample) i -
        (graph sample).step u (fun j => reference j sample) i) 2 μ :=
    memLp_weighted_reply_sub (w i) (fun j z => u z (radius j)) κ hu
      (B i) (X k) reference (hX k) href hk
  have herr : ∀ k i, MemLp (err k i) 2 μ := by
    intro k
    induction k with
    | zero => exact hinit
    | succ k ih =>
      intro i
      apply ((hdiff k ih i).add (hres i)).ae_eq
      filter_upwards with sample
      change (graph sample).step u (fun j => X k j sample) i -
          (graph sample).step u (fun j => reference j sample) i +
          ((graph sample).step u (fun j => reference j sample) i - reference i sample) = _
      simp only [sub_add_sub_cancel]
      rfl
  refine ⟨herr, ?_⟩
  intro N
  apply Collocation.error_le_uniform_finite_sum _ _ _ N (mul_nonneg κ.coe_nonneg hA)
  intro k _
  change ‖fun i => (herr (k+1) i).toLp (err (k+1) i)‖ ≤
    (κ : ℝ) * A * ‖fun i => (herr k i).toLp (err k i)‖ + R
  apply (pi_norm_le_iff_of_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg κ.coe_nonneg hA) (norm_nonneg _)) hR)).2
  intro i
  have hstep := norm_toLp_weighted_reply_sub_le (w i) (fun j z => u z (radius j))
    κ (hrow i) hu (B i) (X k) reference (hX k) href (herr k) (hdiff k (herr k) i)
  have hid : (herr (k+1) i).toLp (err (k+1) i) =
      (hdiff k (herr k) i).toLp (fun sample =>
        (graph sample).step u (fun j => X k j sample) i -
        (graph sample).step u (fun j => reference j sample) i) +
      (hres i).toLp (fun sample => B i sample +
        ∑ j, w i j • u (reference j sample) (radius j) - reference i sample) := by
    apply Lp.ext
    filter_upwards [(herr (k+1) i).coeFn_toLp,
      (hdiff k (herr k) i).coeFn_toLp, (hres i).coeFn_toLp,
      Lp.coeFn_add ((hdiff k (herr k) i).toLp _) ((hres i).toLp _)] with sample he hd hr ha
    simp only [he, ha, Pi.add_apply, hd, hr]
    change _ = (graph sample).step u (fun j => X k j sample) i -
        (graph sample).step u (fun j => reference j sample) i +
        ((graph sample).step u (fun j => reference j sample) i - reference i sample)
    rw [sub_add_sub_cancel]
    rfl
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hstep (hresBound i))

end AcceleratedLogConcave.Numerics.AffineResidual
end AffineResidualRmsRmsHelpers

noncomputable section AffineResidualRmsRms
open MeasureTheory Set
open scoped BigOperators ContDiff NNReal
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph

namespace AcceleratedLogConcave.Numerics.AffineResidual
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {μ : Measure Ω} {m : ℕ}

namespace MeanRms

omit [CompleteSpace E] in
/-- Evaluation of the actual mean graph after cancellation of its arbitrary
raw common anchor. The primitive correspondence is required only at stored
positive radii; it supplies genuine Lp primitive outputs. -/
theorem rawResidual_ae (G : MeanGeometry m) (u : E → ℝ → E) (x : Ω → E)
    (r σ : ℝ) (hr : 0 < r) (uLp : Lp E 2 μ → ℝ → Lp E 2 μ)
    (y0 g0 : Lp E 2 μ) (ζ : Fin m → G.Kernel → Lp E 2 μ)
    (C : Mean.Curves G (Lp E 2 μ)) (hu : PrimitiveLpCorrespondence u x uLp)
    (i : G.MeanNode) :
    rawResidual G u x r σ y0 g0 ζ C i =ᵐ[μ]
      (((G.graph r σ (0 : Lp E 2 μ) y0 g0 ζ).step uLp (C.reference G 0 r) i -
        C.reference G 0 r i : Lp E 2 μ) : Ω → E) := by
  classical
  let Q : G.MeanNode → Lp E 2 μ := fun j => uLp (C.reference G 0 r j) (G.radius r j)
  let B : Lp E 2 μ := ∑ a : G.Anchor,
    G.centerForm r σ i (.inl a) • G.anchorValues y0 g0 ζ a
  have hB := coeFn_weighted_sum (fun a : G.Anchor => G.centerForm r σ i (.inl a))
    (G.anchorValues y0 g0 ζ)
  have hQ : ∀ᵐ sample ∂μ, ∀ j, Q j sample =
      u (rawReference G x r C j sample) (G.radius r j) :=
    ae_all_iff.mpr (fun j => hu (C.reference G 0 r j) (G.radius r j) (G.radius_pos r hr j))
  have hsum := coeFn_weighted_sum (G.matrix r σ i) Q
  have hanchor (a : G.Anchor) (sample : Ω) :
      G.anchorValues y0 g0 ζ a sample =
        G.anchorValues (y0 sample) (g0 sample) (fun b ρ => ζ b ρ sample) a := by
    rcases a with _ | _ | ⟨b,ρ⟩ <;> rfl
  have heq : (G.graph r σ (0 : Lp E 2 μ) y0 g0 ζ).step uLp (C.reference G 0 r) i =
      B + ∑ j, G.matrix r σ i j • Q j := by
    simp only [FiniteGraph.step_eq, MeanGeometry.graph, MeanGeometry.direct, zero_add]
    rfl
  rw [heq]
  filter_upwards [hB, hQ, hsum, Lp.coeFn_add B (∑ j, G.matrix r σ i j • Q j),
    Lp.coeFn_sub (B + ∑ j, G.matrix r σ i j • Q j) (C.reference G 0 r i)]
    with sample hb hq hs ha hd
  simp only [Pi.add_apply] at ha
  simp only [Pi.sub_apply] at hd
  rw [hd, ha]
  rw [hs]
  change _ = (∑ a : G.Anchor, G.centerForm r σ i (.inl a) • G.anchorValues y0 g0 ζ a) sample + _ - _
  rw [hb]
  simp only [hanchor, hq]
  simp only [rawResidual, rawReference, FiniteGraph.step_eq, MeanGeometry.graph,
    MeanGeometry.direct, add_assoc, add_sub_add_left_eq_sub]

/-- The actual Banach-space mean residual bound transfers to raw residuals via
its proved finite-graph evaluation identity. The absolute primitive-output
correspondence remains an explicit upstream hypothesis. -/
theorem meanResidual (G : MeanGeometry m) : ResidualStatement (μ := μ) (E := E) G := by
  intro hm r σ h₀ l v hr hσ hh₀ hl hv hmesh u x uLp y0 g0 ζ C D hu heq hreg
  let Z (i : G.MeanNode) : Lp E 2 μ :=
    (G.graph r σ 0 y0 g0 ζ).step uLp (C.reference G 0 r) i - C.reference G 0 r i
  have hid (i : G.MeanNode) : rawResidual G u x r σ y0 g0 ζ C i =ᵐ[μ] (Z i : Ω → E) :=
    rawResidual_ae G u x r σ hr uLp y0 g0 ζ C hu i
  let hres (i : G.MeanNode) : MemLp (rawResidual G u x r σ y0 g0 ζ C i) 2 μ :=
    (Lp.memLp (Z i)).ae_eq (hid i).symm
  refine ⟨hres, ?_⟩
  intro i
  rw [toLp_eq_of_ae (hres i) (hid i)]
  exact Mean.meanResidual G hm r σ h₀ l v hr hσ hh₀ hl hv hmesh
    uLp 0 y0 g0 ζ C D heq hreg i

end MeanRms

namespace SamplingLpReference
variable {S : SamplingGeometry m} {r : ℝ} {u : E → ℝ → E} {x y0 : Ω → E}
variable (P : SamplingLpReference μ S r u x y0)

omit [CompleteSpace E] in
/-- The centered reply representation suffices because the actual row reproduces
constants exactly. No regularity or moments of the raw baseline are needed. -/
theorem residualIdentity : P.residualIdentityTarget := by
  intro hm i
  have hi := S.mesh.location_mem_interval m i
  have hsumrow : (∑ j : S.Node, S.row (S.mesh.location m i) j) = S.mesh.location m i := by
    simpa only [SamplingGeometry.row, sub_zero] using
      sum_intervalRow S.mesh m hm 0 (S.mesh.location m i)
        ⟨le_rfl, S.samplingEnd_pos.le⟩ ⟨hi.1.le, hi.2.le⟩
  let I : Lp E 2 μ := ∫ t in (0:ℝ)..S.mesh.location m i, P.curve t
  let T : Lp E 2 μ := ∑ j : S.Node, S.row (S.mesh.location m i) j • P.curve (S.mesh.location m j)
  have hreply : ∀ᵐ sample ∂μ, ∀ j : S.Node,
      u (P.reference j sample) (S.radius r j) - P.baseline sample =
        P.curve (S.mesh.location m j) sample :=
    ae_all_iff.mpr (fun j => P.reply _ ⟨(S.mesh.location_mem_interval m j).1.le,
      (S.mesh.location_mem_interval m j).2.le⟩)
  have hflow := P.flow _ ⟨hi.1.le, hi.2.le⟩
  have hsum := coeFn_weighted_sum (S.row (S.mesh.location m i))
    (fun j => P.curve (S.mesh.location m j))
  have hsub := Lp.coeFn_sub I T
  have hscale := Lp.coeFn_smul (r^2*S.mesh.location m i) (I-T)
  filter_upwards [hreply, hflow, hsum, hsub, hscale] with sample hq hy ht hd hs
  simp only [Pi.sub_apply] at hd
  simp only [Pi.smul_apply] at hs
  have hqsum : (∑ j : S.Node, S.row (S.mesh.location m i) j •
      u (P.reference j sample) (S.radius r j)) =
      S.mesh.location m i • P.baseline sample + T sample := by
    have hqeq (j : S.Node) : u (P.reference j sample) (S.radius r j) =
        P.baseline sample + P.curve (S.mesh.location m j) sample := by
      rw [← hq j]
      abel
    simp only [hqeq, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsumrow]
    change _ + _ = _ + T sample
    rw [ht]
  change _ = ((r^2*S.mesh.location m i) • (I-T) : Lp E 2 μ) sample
  rw [hs, hd]
  change (S.graph r (x sample) (y0 sample)).updateFromReplies
      ((S.graph r (x sample) (y0 sample)).collect u (fun j => P.reference j sample)) i -
      P.reference i sample = _
  rw [S.graph_update_eq_centers]
  change x sample + (r*S.mesh.location m i) •
    (y0 sample - r • (∑ j, S.row (S.mesh.location m i) j •
      u (P.reference j sample) (S.radius r j))) -
    (x sample + (r*S.mesh.location m i) • P.path (S.mesh.location m i) sample) = _
  rw [hqsum, hy]
  change _ = (r^2*S.mesh.location m i) • (I sample-T sample)
  module

omit [CompleteSpace E] in
/-- Cell budgets are nonnegative by the actual derivative majorants. -/
theorem cellBudget_nonneg : 0 ≤ P.cellBudget := by
  apply Finset.sum_nonneg
  intro c _
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (pow_nonneg (S.mesh.length_pos c).le _)) (P.cellBound_nonneg c))
    (Nat.cast_nonneg _)

/-- Banach quadrature applies directly to the genuine centered Lp curve. -/
theorem norm_lpDefect_le (hm : 1 ≤ m) (i : S.Node) :
    ‖P.lpDefect i‖ ≤ r^2 * samplingEnd S.τ * P.cellBudget := by
  have hi := S.mesh.location_mem_interval m i
  have hquad := intervalRowDefect (E := Lp E 2 μ) S.mesh m hm 0 (S.mesh.location m i)
    ⟨le_rfl, S.samplingEnd_pos.le⟩ ⟨hi.1.le, hi.2.le⟩
    P.curve P.cellBound ⟨P.cellBound_nonneg, P.smooth, P.deriv_bound⟩
  rw [lpDefect, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg r) hi.1.le)]
  exact (mul_le_mul_of_nonneg_left hquad (mul_nonneg (sq_nonneg r) hi.1.le)).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hi.2.le (sq_nonneg r)) P.cellBudget_nonneg)

/-- Membership is obtained from the proved actual residual identity. -/
theorem residualBound : P.residualBoundTarget := by
  intro hm _
  let hres (i : S.Node) : MemLp (P.rawResidual i) 2 μ :=
    (Lp.memLp (P.lpDefect i)).ae_eq (P.residualIdentity hm i).symm
  refine ⟨hres, ?_⟩
  change ‖fun i => (hres i).toLp (P.rawResidual i)‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg r) S.samplingEnd_pos.le) P.cellBudget_nonneg)).2
  intro i
  rw [toLp_eq_of_ae (hres i) (P.residualIdentity hm i)]
  exact P.norm_lpDefect_le hm i

/-- Actual sampling iterates inherit the difference-only residual and contraction
bounds, and produce every required error-membership witness. -/
theorem iterateBound (κ : ℝ≥0) : P.iterateBoundTarget κ := by
  intro hm hr hu hB href hinit
  obtain ⟨hres, hresBound⟩ := P.residualBound hm hr
  have hR := mul_nonneg (mul_nonneg (sq_nonneg r) S.samplingEnd_pos.le) P.cellBudget_nonneg
  have hrows := S.sum_abs_matrix_le (by omega : 0 < m) r hr.le (0 : E) 0
  have hresNode (i : S.Node) : ‖(hres i).toLp (P.rawResidual i)‖ ≤
      r^2 * samplingEnd S.τ * P.cellBudget :=
    (norm_le_pi_norm (fun j => (hres j).toLp (P.rawResidual j)) i).trans hresBound
  exact raw_affine_iterate_bound
    (fun i sample => (S.graph r (x sample) (y0 sample)).direct i)
    (S.graph r (0 : E) 0).matrix (S.radius r) u P.reference κ (r^2)
    (r^2 * samplingEnd S.τ * P.cellBudget) (sq_nonneg r) hR hrows hu hB href
    hinit hres hresNode

end SamplingLpReference
end AcceleratedLogConcave.Numerics.AffineResidual
end AffineResidualRmsRms
