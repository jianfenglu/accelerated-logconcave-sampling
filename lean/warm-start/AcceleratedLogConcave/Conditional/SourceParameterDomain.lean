import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions.SumProd

/-! The source parameter domain carries its relative topology. The radius
constraint is non-strict, so the equality boundary is retained. -/
namespace AcceleratedLogConcave.Conditional

abbrev SourceParameters (E : Type*) (ell : ℝ) :=
  {p : E × ℝ × ℝ // 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2.1 ^ 2 * ell ≤ 1 / 2}

namespace SourceParameters
variable {E : Type*} {ell : ℝ}

def center (p : SourceParameters E ell) : E := p.val.1
def radius (p : SourceParameters E ell) : ℝ := p.val.2.1
def width (p : SourceParameters E ell) : ℝ := p.val.2.2

theorem radius_pos (p : SourceParameters E ell) : 0 < p.radius := p.property.1
theorem width_pos (p : SourceParameters E ell) : 0 < p.width := p.property.2.1
theorem small (p : SourceParameters E ell) : p.radius ^ 2 * ell ≤ 1 / 2 :=
  p.property.2.2

variable [TopologicalSpace E]
@[continuity] theorem continuous_center : Continuous (center (E := E) (ell := ell)) :=
  continuous_subtype_val.fst
@[continuity] theorem continuous_radius : Continuous (radius (E := E) (ell := ell)) :=
  continuous_subtype_val.snd.fst
@[continuity] theorem continuous_width : Continuous (width (E := E) (ell := ell)) :=
  continuous_subtype_val.snd.snd

end SourceParameters
end AcceleratedLogConcave.Conditional
