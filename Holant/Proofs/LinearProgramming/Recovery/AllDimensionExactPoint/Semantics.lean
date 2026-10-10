import Holant.Proofs.LinearProgramming.Recovery.AllDimensionExactPoint.Programs

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.AllDimensionExactPoint
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP
open scoped BigOperators
namespace Semantics
noncomputable section

theorem response (d : Codec.Input) : Codec.Response d.val (Programs.top d) := by
  by_cases h0 : d.val.dimension=0
  · rw [Programs.zero_branch d h0]
    exact LowDimension.ZeroDim.response d.val h0
  · by_cases h1 : d.val.dimension=1
    · rw [Programs.one_branch d h1]
      exact LowDimension.OneDim.response d.val h1
    · have hn : 2≤d.val.dimension := by omega
      rw [Programs.high_branch d hn]
      have hr := SuccessiveFaceMachine.Source.response (Programs.prepareInput d)
      rw [Programs.prepared_original d hn] at hr
      exact hr

theorem some_sound (d : Codec.Input) (xs : List ℚ) (he : Programs.top d=some xs) :
    Codec.Solution d.val xs := by
  have hr := response d
  rw [he] at hr
  exact hr
theorem same_common_vector (d : Codec.Input) (xs : List ℚ) (he : Programs.top d=some xs) :
    xs.length=d.val.dimension ∧
    (∀ i, ∑ j, (d.val.coefficient i j:ℚ)*Codec.point d.val xs j=d.val.constant i) ∧
    (∀ j, 0≤Codec.point d.val xs j ∧ Codec.point d.val xs j≤1) := some_sound d xs he

theorem none_iff (d : Codec.Input) : Programs.top d=none ↔ ¬∃ x, Codec.Feasible d.val x := by
  constructor
  · intro he
    have hr := response d
    rw [he] at hr
    exact hr
  · intro hn
    cases he : Programs.top d with
    | none => rfl
    | some xs =>
      have hs := some_sound d xs he
      exact False.elim (hn ⟨Codec.point d.val xs,hs.2⟩)

theorem complete (d : Codec.Input) (hf : ∃ x, Codec.Feasible d.val x) :
    ∃ xs, Programs.top d=some xs ∧ Codec.Solution d.val xs := by
  cases he : Programs.top d with
  | none => exact False.elim (((none_iff d).mp he) hf)
  | some xs => exact ⟨xs,rfl,some_sound d xs he⟩
theorem complete_iff (d : Codec.Input) :
    (∃ xs, Programs.top d=some xs ∧ Codec.Solution d.val xs) ↔ ∃ x, Codec.Feasible d.val x := by
  constructor
  · rintro ⟨xs,_,hs⟩
    exact ⟨Codec.point d.val xs,hs.2⟩
  · exact complete d

end
end Semantics
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.AllDimensionExactPoint
