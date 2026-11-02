import AcceleratedLogConcave.Tensor.NetworkRecipient

/-! Full principal integration-by-parts as a sum of actual recipient networks. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators ContDiff
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction CoordinateReduction
variable {n D : ℕ} {Edge : Type*} [Fintype Edge]
variable (g : Graph n Edge) (p : Fin (n+1))

private theorem prod_other (f : Fin (n+1) → ℝ) :
    (∏ v ∈ Finset.univ.erase p, f v) = ∏ v : {v : Fin (n+1) // v ≠ p}, f v :=
  Finset.prod_subtype _ (by simp) f

private theorem prod_other_erase (q : {v : Fin (n+1) // v ≠ p}) (f : Fin (n+1) → ℝ) :
    (∏ v ∈ Finset.univ.erase q, f v.val) =
      ∏ v ∈ (Finset.univ.erase p).erase q.val, f v := by
  apply Finset.prod_bij (fun v _ => v.val)
  · intro v hv
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨v.property, Finset.mem_univ _⟩⟩
    intro h
    exact (Finset.mem_erase.mp hv).1 (Subtype.ext h)
  · intro a _ b _ h
    exact Subtype.ext h
  · intro v hv
    refine ⟨⟨v,(Finset.mem_erase.mp (Finset.mem_erase.mp hv).2).1⟩,?_,rfl⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    intro h
    exact (Finset.mem_erase.mp hv).1 (congrArg Subtype.val h)
  · intro v _; rfl

/-- The actual coordinate formal-adjoint tensor, not an assumed integration certificate. -/
def adjointCoordinateTensor (H : EuclideanSpace ℝ (Fin D) → ℝ)
    (A : EuclideanSpace ℝ (Fin D) → Fin D → Coeff (g.Slot p) D)
    (x : EuclideanSpace ℝ (Fin D)) : Coeff (g.Slot p) D :=
  WithLp.toLp 2 (fun a => adjointField H (coordinateDirection D) (fun k y => A y k a) x)

/-- Principal IBP chooses every different occurrence, and each term is the integral
of its literal added-edge graph. Analytic hypotheses are solely smoothness and actual
product integrability; no global reduction equality is supplied. -/
theorem integral_adjoint_network
    {μ : Measure (EuclideanSpace ℝ (Fin D))} [μ.IsAddHaarMeasure]
    (H : EuclideanSpace ℝ (Fin D) → ℝ) (hH : ContDiff ℝ ∞ H)
    (hZ : Integrable (fun x => Real.exp (-H x)) μ)
    (T : EuclideanSpace ℝ (Fin D) → g.Tensors D)
    (A : EuclideanSpace ℝ (Fin D) → Fin D → Coeff (g.Slot p) D)
    (hA : ∀ k a, ContDiff ℝ ∞ (fun x => A x k a))
    (hT : ∀ v a, Differentiable ℝ (fun x => T x v a))
    (hparent : ∀ x, T x p = g.adjointCoordinateTensor p H A x)
    (hi : ∀ c : (Option Edge → Fin D), ∀ k : Fin D,
      ProductIntegrability (μ.tilted (fun x => -H x)) (fun _ : Unit => (0 : EuclideanSpace ℝ (Fin D))) [] H
        (fun x => A x k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)))
        (coordinateDirection D k)
        (fun q : {v : Fin (n+1) // v ≠ p} => fun x => g.wireValue (T x) c q.val)) :
    (∫ x, g.coordinateEval D (T x) ∂μ.tilted (fun x => -H x)) =
      ∑ q : {v : Fin (n+1) // v ≠ p}, ∫ x,
        (g.recipientGraph p q.val (Ne.symm q.property)).coordinateEval D
          (g.principalRecipientFamily p q.val (Ne.symm q.property) T A x)
        ∂μ.tilted (fun x => -H x) := by
  have hp (c : Option Edge → Fin D) (x : EuclideanSpace ℝ (Fin D)) :
      (∏ v, g.wireValue (T x) c v) =
        adjointField H (coordinateDirection D) (fun k y => A y k
          (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val))) x *
        ∏ q : {v : Fin (n+1) // v ≠ p}, g.wireValue (T x) c q.val := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), prod_other p]
    congr 1
    unfold wireValue
    rw [hparent]
    rfl
  have hc (c : Option Edge → Fin D) : Integrable (fun x => ∏ v, g.wireValue (T x) c v)
      (μ.tilted (fun x => -H x)) := by
    simp_rw [hp c]
    simpa only [partialAlong] using integrable_decorated_field_mul_prod
      (μ.tilted (fun x => -H x)) (fun _ : Unit => (0 : EuclideanSpace ℝ (Fin D))) [] hH
      (coordinateDirection D) _ (fun k => hA k _) _ (hi c)
  have hlocal (c : Option Edge → Fin D) :
      (∫ x, ∏ v, g.wireValue (T x) c v ∂μ.tilted (fun x => -H x)) =
        ∑ k : Fin D, ∑ q : {v : Fin (n+1) // v ≠ p}, ∫ x,
          A x k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
          dir (coordinateDirection D k) (fun y => g.wireValue (T y) c q.val) x *
          ∏ v ∈ (Finset.univ.erase p).erase q.val, g.wireValue (T x) c v
          ∂μ.tilted (fun x => -H x) := by
    simp_rw [hp c]
    have hh := integral_decorated_field_mul_prod
      (μ := μ) (fun _ : Unit => (0 : EuclideanSpace ℝ (Fin D))) [] hH
      (coordinateDirection D) (fun k y => A y k
        (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)))
      (fun k => hA k _) (fun q : {v : Fin (n+1) // v ≠ p} => fun x => g.wireValue (T x) c q.val)
      (fun q => hT q.val _) hZ (hi c)
    simpa only [partialAlong, scoreRoutes, List.map_nil, List.sum_nil, Finset.sum_const_zero,
      add_zero, prod_other_erase p] using hh
  have hterms (q : {v : Fin (n+1) // v ≠ p}) (c : Option Edge → Fin D) (k : Fin D) :
      Integrable (fun x =>
        A x k (Sum.elim (fun s : g.InPort p => c s.val) (fun s : g.OutPort p => c s.val)) *
        dir (coordinateDirection D k) (fun y => g.wireValue (T y) c q.val) x *
        ∏ v ∈ (Finset.univ.erase p).erase q.val, g.wireValue (T x) c v)
        (μ.tilted (fun x => -H x)) := by
    simpa only [partialAlong, prod_other_erase p] using (hi c k).recipients q
  have hrec := fun q : {v : Fin (n+1) // v ≠ p} =>
    g.integral_coordinateEval_principalRecipientFamily p q.val (Ne.symm q.property)
      (μ.tilted (fun x => -H x)) T A (hterms q)
  simp_rw [hrec]
  unfold coordinateEval
  change (∫ x, ∑ c : (Option Edge → Fin D), ∏ v, g.wireValue (T x) c v ∂μ.tilted (fun x => -H x)) = _
  rw [integral_finsetSum _ (fun c _ => hc c)]
  change (∑ c : (Option Edge → Fin D), ∫ x, ∏ v, g.wireValue (T x) c v ∂μ.tilted (fun x => -H x)) = _
  simp_rw [hlocal]
  conv_lhs =>
    arg 2
    ext c
    rw [Finset.sum_comm]
  exact Finset.sum_comm
end AcceleratedLogConcave.Tensor.Ordered.Graph
