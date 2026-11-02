import AcceleratedLogConcave.Oracle.MeanChronologicalExecution

/-! Earlier returned references remain jointly unchanged with the complete
original source through every later executed mean layer. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
namespace AcceleratedLogConcave.Oracle.MeanChronologicalPast
open Numerics Numerics.AffineGraph AffineLowering TapeLowering NoisyLayer
open TailOccurrenceCut TailCut CanonicalTapeLaw CanonicalTapeMeasurability
open MeanChronologicalCoupling
local instance canonicalTapeSpace {d c : ℕ} {Γ : Ctx} {τ : Ty} (p : Prog c Γ τ) :
    MeasurableSpace (Tape d p) := tapeSpace d p
local instance canonicalPrefixSpace {d c : ℕ} {Γ Δ : Ctx} {τ σ : Ty}
    {p : Prog c Γ τ} {q : Prog c Δ σ} (cut : TailCut q p) :
    MeasurableSpace (Prefix d cut) := prefixSpace d cut
section HistoryPersistence
variable {m n a h d : ℕ} (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
  (sampling : ExecutableData) (N : ℕ)
  {A : Type*} [MeasurableSpace A]

/-- All original source coordinates and the first k recorded returned vectors.
Keeping the complete original tape makes this useful for later child errors. -/
def past (k : ℕ) (hk : k≤N)
    (z : History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) :=
  ((z.1.1,z.2), fun j : Fin k => z.1.2.1 ⟨j,lt_of_lt_of_le j.2 hk⟩)

theorem past_measurable (k : ℕ) (hk : k≤N) :
    Measurable (past (d := d) (A := A) M nodes anchors seeds main final sampling N k hk) := by
  exact (measurable_fst.fst.prodMk measurable_snd).prodMk
    (Measurable.of_eval fun j => (measurable_pi_apply _).comp measurable_fst.snd.fst)

variable (r Ds : ℝ) (hr : 0<r) (hDs : 0<Ds)
  (hmass : ∀ i, CovarianceSetup.shiftSq (main i).shiftVector ≤ Ds^2)

variable (σ δ t w : ℝ)

omit [MeasurableSpace A] in
theorem past_record (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (k : ℕ) (hk : k≤N) (j : Fin N) (hj : k≤j)
    (z : (History (d := d) M nodes anchors seeds main final sampling N A × Tape d (Host M nodes anchors seeds main final sampling N)) × (Fin n → Point d)) :
    past M nodes anchors seeds main final sampling N k hk
      (record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs j z) =
    past M nodes anchors seeds main final sampling N k hk z.1 := by
  apply Prod.ext
  · rfl
  · funext i
    apply Function.update_of_ne
    intro h
    have hv := congrArg Fin.val h
    change (i:ℕ) = (j:ℕ) at hv
    omega

variable (L : PrimitiveLaws d) (hL : L.pointDraw = stdGaussian (Point d))
  (x P referencePosition : A → Point d) (hx : Measurable x) (hP : Measurable P)
  (hreference : Measurable referencePosition)
  {F : Point d → ℝ} (hF : ContDiff ℝ 2 F) {ell : ℝ} (hell : 0≤ell)
  (hlo : ∀ z v, 0≤fderiv ℝ (fderiv ℝ F) z v v)
  (hup : ∀ z v, fderiv ℝ (fderiv ℝ F) z v v≤ell*‖v‖^2)

variable (hσ : 0<σ) (hsmall : r^2*ell≤1/2)

theorem step_past (s : Cursor M nodes anchors seeds main final sampling N) (hs : 0<s.remaining)
    (k : ℕ) (hk : k≤N) (j : Fin N) (hj : k≤j)
    (J : FreshChildBatchCoupling.Lower L (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass s hs)) :
    (step M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w s hs j J).map
      (past M nodes anchors seeds main final sampling N k hk) =
    Kernel.deterministic (past M nodes anchors seeds main final sampling N k hk)
      (past_measurable M nodes anchors seeds main final sampling N k hk) := by
  rw [MeanChronologicalCoupling.step,← Kernel.map_comp_right _
    (record_measurable M nodes anchors seeds main final sampling N r Ds hr hDs hmass L σ δ t w s hs j)
    (past_measurable M nodes anchors seeds main final sampling N k hk)]
  have he : past (d := d) (A := A) M nodes anchors seeds main final sampling N k hk ∘
      record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs j =
      past M nodes anchors seeds main final sampling N k hk ∘ Prod.fst := by
    funext z
    exact past_record M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w s hs k hk j hj z
  rw [he,Kernel.map_comp_right _ measurable_fst (past_measurable M nodes anchors seeds main final sampling N k hk),
    ← Kernel.fst_eq,adjoin_original,Kernel.id_map]

variable
  (J : ∀ (j : ℕ) (hj : j<N), FreshChildBatchCoupling.Lower L
    (data M nodes anchors seeds main final sampling N r Ds hr hDs hmass
      (stage M nodes anchors seeds main final sampling N j hj.le).1
      (stage_positive M nodes anchors seeds main final sampling N j hj)))

/-- Later actual layers preserve all already recorded returned references
jointly with the full original seed. This is a kernel identity, before choosing
a probability law or an external center. -/
theorem iteration_past (k l : ℕ) (hk : k≤N) (hkl : k≤l) (hl : l≤N) :
    (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J l hl).map
      (past M nodes anchors seeds main final sampling N k hk) =
    (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J k hk).map
      (past M nodes anchors seeds main final sampling N k hk) := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    rw [iteration,Kernel.map_comp,step_past M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w L hL x P referencePosition hx hP hreference hF hell hlo hup hσ hsmall
      _ _ k hk ⟨l,by omega⟩ hkl,Kernel.deterministic_comp_eq_map]
    exact ih (by omega)
/-- Read any completed prefix of returned references from the final finite
loop law without changing its joint law with the complete original source. -/
theorem kernel_past (k : ℕ) (hk : k≤N) (μ : Measure (A × Tape d (Host M nodes anchors seeds main final sampling N))) :
    (kernel M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J ∘ₘ μ).map
      (past M nodes anchors seeds main final sampling N k hk) =
    (iteration M nodes anchors seeds main final sampling N r Ds hr hDs hmass L hL x P referencePosition hx hP hreference hF hell hlo hup σ hσ hsmall δ t w J k hk ∘ₘ
      (μ.map (MeanInitialComparison.prepare M nodes anchors seeds main final sampling N))).map (past M nodes anchors seeds main final sampling N k hk) := by
  rw [kernel,← Measure.comp_assoc,Measure.deterministic_comp_eq_map,Measure.map_comp _ _ (past_measurable M nodes anchors seeds main final sampling N k hk),
    iteration_past M nodes anchors seeds main final sampling N r Ds hr hDs hmass σ δ t w L hL x P referencePosition hx hP hreference hF hell hlo hup hσ hsmall J k N hk hk le_rfl,
    Measure.map_comp _ _ (past_measurable M nodes anchors seeds main final sampling N k hk)]

end HistoryPersistence
end AcceleratedLogConcave.Oracle.MeanChronologicalPast
