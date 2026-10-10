import Holant.Proofs.Hardness.BinaryCSPProgrammeMachine
import Holant.Proofs.Hardness.BinaryThreeSupportFilter
import Holant.Proofs.Hardness.ThreeModeAnnihilatorFilterSemantics

/-! Exact support-count correctness of the actual positive-query programme.
All field values and the final output retain the original fixed-field codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot BinaryCSPProgrammeCore
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
local instance : Fintype Bool := Bool.fintype
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b c : K) (f : Bool→Bool→K)
local instance : DecidableEq K := Classical.decEq K

def moments (r : Raw) (k : ℕ) : K :=
  ∑ x : Fin r.variables→Bool,(BinaryCSPProgrammeValue.weight f r x)^k

def support (r : Raw) : K :=
  ∑ x : Fin r.variables→Bool,if BinaryCSPProgrammeValue.weight f r x=0 then 0 else 1

@[simp] theorem moments_zero (r : Raw) : moments f r 0=total (K:=K) r := by
  simp [moments,total]

theorem roots_eq (n : ℕ) : R.roots a b c n=BinaryThreeSupportFilter.cubeRoots n a b c := by
  simp [BinaryCSPProgrammeRoots.roots,BinaryCSPProgrammeRoots.indices,
    BinaryCSPProgrammeRoots.monomial,BinaryThreeSupportFilter.cubeRoots,
    List.map_flatMap,List.map_map,Function.comp_def]

theorem state_table (r : Raw) : state a b c f r=
    ((R.roots a b c r.edges.length,
      ThreeModeAnnihilatorFilterSemantics.table ((R.roots a b c r.edges.length).length+1) (moments f r)),(0,1)) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change total r::answers f r=_
      rw [ThreeModeAnnihilatorFilterSemantics.table,List.ofFn_succ]
      congr 1
      · exact (moments_zero f r).symm
      · apply List.ext_getElem
        · simp [answers,BinaryCSPProgrammeRepeat.queries,BinaryCSPProgrammeRepeat.sampleCount]
          ring
        · intro i hi hj
          simp only [answers,BinaryCSPProgrammeRepeat.queries,List.getElem_map,
            List.getElem_range,List.getElem_ofFn,Fin.val_succ]
          exact BinaryCSPProgrammeValue.repeat_value f r i
  · rfl

theorem value_formula (r : Raw) : interpolatedValue F a b c f r=
    total r-ThreeModeAnnihilator.differenceFilter (R.roots a b c r.edges.length) (moments f r) 0 /
      BinaryThreeSupportFilter.denominator (R.roots a b c r.edges.length) := by
  have hround := (ThreeModeFilter.list_counts_le_bytes F (state a b c f r)).1
  change (R.roots a b c r.edges.length).length≤((S.encoding F).encode (state a b c f r)).length at hround
  unfold interpolatedValue Loop.result ThreeModeFilterLoop.value
  rw [state_table a b c f r]
  rw [ThreeModeAnnihilatorFilterSemantics.iterate_stable _ _ _ _ _ (by
    simpa only [←state_table a b c f r] using hround)]
  simp [BinaryThreeSupportFilter.denominator]

theorem weight_product (r : Raw) (x : Fin r.variables→Bool) :
    BinaryCSPProgrammeValue.weight f r x=
      ∏ i : Fin r.edges.length,f (BinaryCSPProgrammeValue.assignment r x (r.edges.get i).1)
        (BinaryCSPProgrammeValue.assignment r x (r.edges.get i).2) := by
  unfold BinaryCSPProgrammeValue.weight
  rw [←List.prod_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

theorem support_correct (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hf : ∀ x y,f x y=0 ∨ f x y=a ∨ f x y=b ∨ f x y=c) (r : Raw) :
    interpolatedValue F a b c f r=support f r := by
  rw [value_formula,roots_eq]
  have h := BinaryThreeSupportFilter.count_nonzero (fun x => BinaryCSPProgrammeValue.weight f r x)
    (BinaryThreeSupportFilter.cubeRoots r.edges.length a b c)
    (BinaryThreeSupportFilter.cubeRoots_nonzero _ ha hb hc) (by
      intro x hx
      rw [weight_product f r x] at hx ⊢
      obtain ⟨i,hi⟩ := BinaryThreeSupportAnnihilator.product_spectrum
        (fun i : Fin r.edges.length => f (BinaryCSPProgrammeValue.assignment r x (r.edges.get i).1)
          (BinaryCSPProgrammeValue.assignment r x (r.edges.get i).2)) a b c (fun i => hf _ _) hx
      rw [hi]
      exact BinaryThreeSupportFilter.monomial_mem _ a b c i)
  have hm : (fun j => ∑x : Fin r.variables→Bool,BinaryCSPProgrammeValue.weight f r x^j)=moments f r := by
    funext j
    rfl
  rw [hm] at h
  simpa [support,total] using h.symm

/-- The genuine length-controlled reduction now targets a semantic support
count, with no evaluator, runtime certificate or completed trace as input. -/
def supportControlled (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hf : ∀ x y,f x y=0 ∨ f x y=a ∨ f x y=b ∨ f x y=c) :
    LengthControlledOracleReduction encoding F.encoding encoding F.encoding (support f) (V.value f) where
  reduction := {
    machine := (controlled F a b c f).reduction.machine
    time := (controlled F a b c f).reduction.time
    correct oracle ho r := by
      rw [←support_correct F a b c f ha hb hc hf r]
      exact (controlled F a b c f).reduction.correct oracle ho r }
  targetOutput := (controlled F a b c f).targetOutput
  queryBound := (controlled F a b c f).queryBound
  safeQuery := (controlled F a b c f).safeQuery

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMachine
