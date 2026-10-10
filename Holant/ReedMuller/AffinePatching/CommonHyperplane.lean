import Holant.ReedMuller.RadonAccess.Directions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod

/-! A source-accessible direction annihilating a bounded collection of actual
vectors. Rank-nullity excludes only the zero/all-one line, not an assumed
list of available hyperplanes. -/
namespace Holant.ReedMuller.AffinePatching
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def constraintMap (w : Fin k → BinaryVector n) :
    BinaryVector n →ₗ[ZMod 2] BinaryVector (k+1) where
  toFun x := Fin.cons (dot x (ones n)) (fun i => dot x (w i))
  map_add' := by
    intro x y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [dot_add_left]
  map_smul' := by
    intro c x
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [dot_smul_left]

 theorem exists_accessible_orthogonal (hk : k+3≤n) (w : Fin k → BinaryVector n) :
    ∃ v : BinaryVector n,Accessible v ∧ ∀ i,dot v (w i)=0 := by
  let L := constraintMap w
  have hdim : Module.finrank (ZMod 2) (BinaryVector n)=n := by simp [BinaryVector]
  have hcod : Module.finrank (ZMod 2) (BinaryVector (k+1))=k+1 := by simp [BinaryVector]
  have hr := LinearMap.finrank_range_add_finrank_ker (K:=ZMod 2) L
  rw [hdim] at hr
  have hb : Module.finrank (ZMod 2) (LinearMap.range L)≤k+1 := by
    simpa only [hcod] using (Submodule.finrank_le (LinearMap.range L))
  have hline : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({ones n}:Set (BinaryVector n)))≤1 := by
    simpa using (finrank_span_le_card ({ones n}:Set (BinaryVector n)))
  have hn : ¬LinearMap.ker L≤Submodule.span (ZMod 2) ({ones n}:Set (BinaryVector n)) := by
    intro h
    have hc := (Submodule.finrank_mono h).trans hline
    omega
  change ¬∀ v,v∈LinearMap.ker L → v∈Submodule.span (ZMod 2) ({ones n}:Set (BinaryVector n)) at hn
  push_neg at hn
  obtain ⟨v,hv,hnot⟩ := hn
  have he : L v=0 := hv
  have he0 := congrFun he 0
  have hfirst : dot v (ones n)=0 := he0
  refine ⟨v,⟨?_,?_,?_⟩,?_⟩
  · rwa [dot_comm]
  · intro hz
    subst v
    exact hnot (Submodule.zero_mem _)
  · intro ho
    subst v
    exact hnot (Submodule.subset_span (Set.mem_singleton _))
  · intro i
    exact congrFun he i.succ

end
end Holant.ReedMuller.AffinePatching
